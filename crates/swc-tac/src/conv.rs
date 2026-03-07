//! Conversion from CFG (Control Flow Graph) to TAC (Three-Address Code).
//!
//! This module handles the transformation from the higher-level CFG representation
//! (which uses SWC AST expressions) to the lower-level TAC representation (which
//! uses simple identifiers and operations).
//!
//! # Conversion Process
//!
//! The conversion process:
//! 1. Transforms SWC AST expressions into TAC items
//! 2. Breaks down complex expressions into simple assignments
//! 3. Allocates temporary registers for intermediate values
//! 4. Preserves control flow structure (blocks, jumps, branches)
//! 5. Handles pattern destructuring and complex assignments
//!
//! # Key Type
//!
//! [`ToTACConverter`] - The main converter struct that maintains state during conversion

use crate::*;
use std::mem::replace;
use swc_ecma_ast::{
    ArrayPat, AssignPat, AssignTargetPat, BindingIdent, CallExpr, ObjectPat, ObjectPatProp,
};

#[non_exhaustive]
pub struct ToTACConverterCore<'a> {
    pub mapper: Mapper<'a>,
}
impl ToTACConverterCore<'_> {
    fn convert_call_expr(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        call: &CallExpr,
    ) -> Result<(
        TCallee<Ident>,
        Vec<SpreadOr<(Atom, SyntaxContext)>>,
        TBlockId,
    ), crate::Error> {
        let callee = match &call.callee {
            Callee::Import(_) => TCallee::Import,
            Callee::Super(_) => TCallee::Super,
            Callee::Expr(e) => match e.as_ref() {
                Expr::Ident(i) if i.sym == "eval" && !i.optional => TCallee::Eval,
                Expr::Member(m) => {
                    let r#fn;
                    (r#fn, t) = self.expr(o, t, &m.obj)?;
                    match &m.prop {
                        MemberProp::PrivateName(p) => TCallee::PrivateMember {
                            func: r#fn,
                            member: Private {
                                sym: p.name.clone(),
                                ctxt: Default::default(),
                                span: p.span,
                            },
                        },
                        _ => {
                            let member;
                            (member, t) = self.expr(o, t, &imp(m.prop.clone()))?;
                            TCallee::Member { func: r#fn, member }
                        }
                    }
                }
                _ => {
                    let r#fn;
                    (r#fn, t) = self.expr(o, t, e.as_ref())?;
                    TCallee::Val(r#fn)
                }
            },
            _ => return Err(crate::Error::Unsupported { file: file!(), line: line!() }),
        };
        let args: Vec<SpreadOr<Ident>> = call
            .args
            .iter()
            .map(|a| {
                let arg;
                (arg, t) = self.expr(o, t, &a.expr)?;
                Ok(SpreadOr {
                    value: arg,
                    is_spread: a.spread.is_some(),
                })
            })
            .collect::<Result<_, crate::Error>>()?;
        Ok((callee, args, t))
    }
    pub fn stmt(&mut self, o: &mut TCfg, mut t: TBlockId, s: &Stmt) -> Result<TBlockId, crate::Error> {
        match s {
            Stmt::Expr(e) => {
                (_, t) = self.expr(o, t, &e.expr)?;
                Ok(t)
            }
            Stmt::Empty(_) => Ok(t),
            Stmt::Decl(d) => match d {
                swc_ecma_ast::Decl::Class(f) => {
                    let c;
                    (c, t) = self.class(o, t, &f.class)?;
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id {
                            id: f.ident.clone().into(),
                        },
                        flags: Default::default(),
                        right: Item::Just { id: c },
                        span: f.span(),
                    });
                    o.decls.insert(f.ident.clone().into());
                    Ok(t)
                }
                swc_ecma_ast::Decl::Fn(f) => {
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id {
                            id: f.ident.clone().into(),
                        },
                        flags: Default::default(),
                        right: Item::Func {
                            func: f.function.as_ref().clone().try_into()?,
                            arrow: false,
                        },
                        span: f.span(),
                    });
                    o.decls.insert(f.ident.clone().into());
                    Ok(t)
                }
                swc_ecma_ast::Decl::Var(var_decl) => {
                    for var_decl in var_decl.decls.iter() {
                        if let Some(e) = &var_decl.init {
                            let f;
                            (f, t) = self.expr(o, t, e)?;
                            t = self.bind(o, t, &var_decl.name, f, true)?;
                        }
                    }
                    Ok(t)
                }
                swc_ecma_ast::Decl::Using(_using_decl) => todo!(),
                swc_ecma_ast::Decl::TsInterface(_ts_interface_decl) => todo!(),
                swc_ecma_ast::Decl::TsTypeAlias(_ts_type_alias_decl) => todo!(),
                swc_ecma_ast::Decl::TsEnum(_ts_enum_decl) => todo!(),
                swc_ecma_ast::Decl::TsModule(_ts_module_decl) => todo!(),
            },
            _ => return Err(crate::Error::Unsupported { file: file!(), line: line!() }),
        }
    }
    pub fn bind(
        &mut self,

        o: &mut TCfg,

        t: TBlockId,
        p: &Pat,
        f: Ident,
        decl: bool,
    ) -> Result<TBlockId, crate::Error> {
        match p {
            Pat::Ident(i2) => self.bind_ident(o, t, i2, f, decl),
            Pat::Object(op) => self.bind_object(o, t, op, f, decl),
            Pat::Assign(ass) => self.bind_assign(o, t, ass, f, decl),
            _ => return Err(crate::Error::Unsupported { file: file!(), line: line!() }),
        }
    }
    pub fn bind_assign(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        assign_pat: &AssignPat,
        f: Ident,
        decl: bool,
    ) -> Result<TBlockId, crate::Error> {
        let g = o.regs.alloc(());
        o.decls.insert(g.clone());
        o.blocks[t].stmts.push(TStmt {
            left: LId::Id { id: g.clone() },
            flags: ValFlags::empty(),
            right: Item::Undef,
            span: assign_pat.span(),
        });
        o.blocks[t].stmts.push(TStmt {
            left: LId::Id { id: g.clone() },
            flags: ValFlags::empty(),
            right: Item::Bin {
                left: f.clone(),
                right: g.clone(),
                op: BinaryOp::EqEqEq,
            },
            span: assign_pat.span(),
        });
        let pp = o.blocks[t].post.clone();
        let gb = o.blocks.alloc(TBlock {
            stmts: Default::default(),
            post: pp.clone(),
        });
        o.blocks[gb].stmts.push(TStmt {
            left: LId::Id { id: g.clone() },
            flags: ValFlags::empty(),
            right: Item::Just { id: f.clone() },
            span: assign_pat.span(),
        });
        let eb = o.blocks.alloc(TBlock {
            stmts: Default::default(),
            post: pp.clone(),
        });
        let h2;
        let ex;
        (h2, ex) = self.expr(o, eb, &assign_pat.right)?;
        o.blocks[ex].stmts.push(TStmt {
            left: LId::Id { id: g.clone() },
            flags: ValFlags::empty(),
            right: Item::Just { id: h2 },
            span: assign_pat.span(),
        });
        let nb = o.blocks.alloc(TBlock {
            stmts: Default::default(),
            post: pp,
        });
        for x in [gb, ex] {
            o.blocks[x].post.term = TTerm::Jmp(nb)
        }
        o.blocks[replace(&mut t, nb)].post.term = TTerm::CondJmp {
            cond: g.clone(),
            if_true: eb,
            if_false: gb,
        };
        self.bind(o, t, &assign_pat.left, g, decl)
    }
    pub fn bind_array(
        &mut self,

        o: &mut TCfg,

        t: TBlockId,
        p: &ArrayPat,
        f: Ident,
        decl: bool,
    ) -> Result<TBlockId, crate::Error> {
        let ps = p.elems.iter().map(|a| a.as_ref()).collect::<Vec<_>>();
        self.bind_array_contents(o, t, ps, p, f, decl)
    }
    pub fn bind_array_contents(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        ps: Vec<Option<&Pat>>,
        p: &(dyn Spanned + '_),
        f: Ident,
        decl: bool,
    ) -> Result<TBlockId, crate::Error> {
        let mut ix = 0;
        let r = loop {
            if let Some(a) = ps.get(ix).and_then(|a| *a) {
                if let Pat::Rest(r) = a {
                    ix += 1;
                    break r;
                }
                let fi = o.regs.alloc(());
                o.decls.insert(fi.clone());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: fi.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Lit {
                        lit: Lit::Num(Number {
                            span: a.span(),
                            value: ix as f64,
                            raw: None,
                        }),
                    },
                    span: a.span(),
                });
                let fi = match fi {
                    v => {
                        let fi = o.regs.alloc(());
                        o.decls.insert(fi.clone());
                        o.blocks[t].stmts.push(TStmt {
                            left: LId::Id { id: fi.clone() },
                            flags: ValFlags::SSA_LIKE,
                            right: Item::Mem {
                                obj: f.clone(),
                                mem: v.clone(),
                            },
                            span: a.span(),
                        });
                        fi
                    }
                };
                t = self.bind(o, t, a, fi, decl)?;
            }
            ix += 1;
            if ix == ps.len() {
                return Ok(t);
            }
        };
        let fi2 = o.regs.alloc(());
        o.decls.insert(fi2.clone());
        o.blocks[t].stmts.push(TStmt {
            left: LId::Id { id: fi2.clone() },
            flags: ValFlags::SSA_LIKE,
            right: Item::StaticSubArray {
                begin: ix,
                end: ps.len() - ix,
                wrapped: f.clone(),
            },
            span: p.span(),
        });
        let fi3 = match fi2.clone() {
            v => {
                let fi2 = o.regs.alloc(());
                o.decls.insert(fi2.clone());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: fi2.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::StaticSubArray {
                        begin: ps.len() - ix,
                        end: 0,
                        wrapped: v,
                    },
                    span: p.span(),
                });
                fi2
            }
        };
        t = self.bind(o, t, &r.arg, fi3, decl)?;
        let ox = ix;
        while ix != ps.len() {
            // j += 1;
            if let Some(a) = ps.get(ix).and_then(|a| *a) {
                let fi = o.regs.alloc(());
                o.decls.insert(fi.clone());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: fi.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Lit {
                        lit: Lit::Num(Number {
                            span: a.span(),
                            value: (ix - ox) as f64,
                            raw: None,
                        }),
                    },
                    span: a.span(),
                });
                let fi = match fi {
                    v => {
                        let fi = o.regs.alloc(());
                        o.decls.insert(fi.clone());
                        o.blocks[t].stmts.push(TStmt {
                            left: LId::Id { id: fi.clone() },
                            flags: ValFlags::SSA_LIKE,
                            right: Item::Mem {
                                obj: fi2.clone(),
                                mem: v,
                            },
                            span: a.span(),
                        });
                        fi
                    }
                };
                t = self.bind(o, t, a, fi, decl)?;
            }
            ix += 1
            // i += 1;
        }
        Ok(t)
    }
    pub fn bind_object(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        p: &ObjectPat,
        f: Ident,
        decl: bool,
    ) -> Result<TBlockId, crate::Error> {
        let mut a = BTreeSet::new();
        for prop in p.props.iter() {
            match prop {
                swc_ecma_ast::ObjectPatProp::KeyValue(key_value_pat_prop) => {
                    let g;
                    let h;
                    (h, t) = self.member_prop_expr(o, t, &key_value_pat_prop.key.clone().into())?;
                    a.insert(h.clone());
                    g = o.regs.alloc(());
                    o.decls.insert(g.clone());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: g.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Mem {
                            obj: f.clone(),
                            mem: h,
                        },
                        span: prop.span(),
                    });
                    t = self.bind(o, t, &key_value_pat_prop.value, g, decl)?;
                }
                swc_ecma_ast::ObjectPatProp::Assign(assign_pat_prop) => {
                    let g;
                    let h = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: h.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Lit {
                            lit: Lit::Str(Str {
                                span: assign_pat_prop.span,
                                value: assign_pat_prop.key.sym.clone().into(),
                                raw: None,
                            }),
                        },
                        span: prop.span(),
                    });
                    a.insert(h.clone());
                    g = o.regs.alloc(());
                    o.decls.insert(g.clone());
                    match assign_pat_prop.value.as_ref() {
                        None => {
                            o.blocks[t].stmts.push(TStmt {
                                left: LId::Id { id: g.clone() },
                                flags: ValFlags::SSA_LIKE,
                                right: Item::Mem {
                                    obj: f.clone(),
                                    mem: h,
                                },
                                span: prop.span(),
                            });
                        }
                        Some(e) => {
                            o.blocks[t].stmts.push(TStmt {
                                left: LId::Id { id: g.clone() },
                                flags: ValFlags::empty(),
                                right: Item::Bin {
                                    left: h.clone(),
                                    right: f.clone(),
                                    op: BinaryOp::In,
                                },
                                span: prop.span(),
                            });
                            let pp = o.blocks[t].post.clone();
                            let gb = o.blocks.alloc(TBlock {
                                stmts: Default::default(),
                                post: pp.clone(),
                            });
                            o.blocks[gb].stmts.push(TStmt {
                                left: LId::Id { id: g.clone() },
                                flags: ValFlags::empty(),
                                right: Item::Mem {
                                    obj: f.clone(),
                                    mem: h,
                                },
                                span: prop.span(),
                            });
                            let eb = o.blocks.alloc(TBlock {
                                stmts: Default::default(),
                                post: pp.clone(),
                            });
                            let h2;
                            let ex;
                            (h2, ex) = self.expr(o, eb, e)?;
                            o.blocks[ex].stmts.push(TStmt {
                                left: LId::Id { id: g.clone() },
                                flags: ValFlags::empty(),
                                right: Item::Just { id: h2 },
                                span: prop.span(),
                            });
                            let nb = o.blocks.alloc(TBlock {
                                stmts: Default::default(),
                                post: pp,
                            });
                            for x in [gb, ex] {
                                o.blocks[x].post.term = TTerm::Jmp(nb)
                            }
                            o.blocks[replace(&mut t, nb)].post.term = TTerm::CondJmp {
                                cond: g.clone(),
                                if_true: gb,
                                if_false: eb,
                            };
                        }
                    }
                    t = self.bind_ident(o, t, &assign_pat_prop.key, g, decl)?;
                }
                swc_ecma_ast::ObjectPatProp::Rest(_rest_pat) => {}
            }
        }
        for prop in p.props.iter() {
            if let ObjectPatProp::Rest(rest) = prop {
                let g = o.regs.alloc(());
                o.decls.insert(g.clone());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: g.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::StaticSubObject {
                        wrapped: f.clone(),
                        keys: a.iter().cloned().map(PropKey::Computed).collect(),
                    },
                    span: prop.span(),
                });
                t = self.bind(o, t, &rest.arg, g, decl)?;
            }
        }
        Ok(t)
    }
    pub fn bind_ident(
        &mut self,
        o: &mut TCfg,

        t: TBlockId,
        i2: &BindingIdent,
        f: Ident,
        decl: bool,
    ) -> Result<TBlockId, crate::Error> {
        o.blocks[t].stmts.push(TStmt {
            left: LId::Id {
                id: i2.id.clone().into(),
            },
            flags: Default::default(),
            right: Item::Just { id: f },
            span: i2.span,
        });
        if decl {
            o.decls.insert(i2.id.clone().into());
        }
        if let Some(a) = i2.type_ann.as_ref().cloned() {
            o.type_annotations.insert(i2.id.clone().into(), *a.type_ann);
        }
        Ok(t)
    }
    pub fn member_expr(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        s: &MemberExpr,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        let obj;
        (obj, t) = self.expr(o, t, &s.obj)?;
        self.member_prop(o, t, &s.prop, obj)
    }
    pub fn member_prop(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        s: &MemberProp,
        obj: Ident,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        let i = match s {
            MemberProp::PrivateName(p) => Item::PrivateMem {
                obj,
                mem: Private {
                    sym: p.name.clone(),
                    ctxt: self
                        .mapper
                        .privates
                        .get(&p.name)
                        .cloned()
                        .unwrap_or_default(),
                    span: p.span,
                },
            },
            _ => {
                let mem;
                // let e;
                (mem, t) = self.member_prop_expr(o, t, s)?;
                Item::Mem { obj, mem }
            }
        };
        let v = o.regs.alloc(());
        o.blocks[t].stmts.push(TStmt {
            left: LId::Id { id: v.clone() },
            flags: ValFlags::SSA_LIKE,
            right: i,
            span: s.span(),
        });
        o.decls.insert(v.clone());
        Ok((v, t))
    }
    pub fn class(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        s: &Class,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        let superclass = match &s.super_class {
            None => None,
            Some(a) => Some({
                let b2;
                (b2, t) = self.expr(o, t, a)?;
                b2
            }),
        };
        macro_rules! prop_name {
            ( $w:expr , $v:expr => $a:expr) => {
                match $v {
                    v => match $w {
                        w => match $a {
                            swc_ecma_ast::PropName::Ident(ident_name) => (
                                w,
                                PropKey::Lit(PropSym {
                                    sym: ident_name.sym.clone(),
                                    span: ident_name.span,
                                    ctx: PrivateKind::Public,
                                }),
                                v,
                            ),
                            swc_ecma_ast::PropName::Str(s) => {
                                ((
                                    w,
                                    PropKey::Lit(PropSym {
                                        sym: s.value.as_atom().cloned().unwrap(),
                                        span: s.span,
                                        ctx: PrivateKind::Public,
                                    }),
                                    v,
                                ))
                            }
                            swc_ecma_ast::PropName::Num(number) => {
                                return Err(crate::Error::Unsupported { file: file!(), line: line!() })
                            }
                            swc_ecma_ast::PropName::Computed(computed_prop_name) => {
                                let w2;
                                (w2, t) = self.expr(o, t, &computed_prop_name.expr)?;
                                ((w, PropKey::Computed(w2), v))
                            }
                            swc_ecma_ast::PropName::BigInt(big_int) => {
                                return Err(crate::Error::Unsupported { file: file!(), line: line!() })
                            }
                        },
                    },
                }
            };
        }
        let mut members: Vec<(
            MemberFlags,
            PropKey<Ident, PrivateKind>,
            PropVal<Option<(Atom, swc_common::SyntaxContext)>, TFunc>,
        )> = Default::default();
        let mut constructor: Option<TFunc> = Default::default();
        let mut privates = self.mapper.privates.clone();
        let ctx = SyntaxContext::empty().apply_mark(Mark::new());
        for m in s.body.iter() {
            match m {
                ClassMember::PrivateMethod(m) => {
                    privates.insert(m.key.name.clone(), ctx);
                }
                ClassMember::PrivateProp(m) => {
                    privates.insert(m.key.name.clone(), ctx);
                }
                _ => {}
            }
        }
        let mapper = self.mapper.clone();
        let mut mapper = mapper.bud();
        mapper.privates = &privates;
        for m in s.body.iter() {
            match m {
                ClassMember::ClassProp(p) => {
                    members.push(
                        prop_name!(if p.is_static{MemberFlags::STATIC}else{MemberFlags::empty()},PropVal::Item( match p.value.as_ref(){
                                    None => None,
                                    Some(a) => Some({
                            let b2;
                            (b2, t) = self.expr(o, t, a)?;
                            b2
                        }),
                    }) => &p.key),
                    );
                }
                ClassMember::Constructor(c) => {
                    constructor = Some(TFunc::try_from_with_mapper(
                        &(self.mapper.to_cfg)(&Function {
                            body: c.body.clone(),
                            params: c
                                .params
                                .iter()
                                .filter_map(|a| a.as_param())
                                .cloned()
                                .collect(),
                            is_async: false,
                            is_generator: false,
                            span: c.span,
                            decorators: vec![],
                            ctxt: Default::default(),
                            type_params: None,
                            return_type: None,
                        })?,
                        mapper.bud(),
                    )?)
                }
                ClassMember::Method(c) => {
                    let f =
                        TFunc::try_from_with_mapper(&(mapper.to_cfg)(&c.function)?, mapper.bud())?;
                    members.push(prop_name!(if c.is_static{MemberFlags::STATIC}else{MemberFlags::empty()}, match &c.kind{
                        swc_ecma_ast::MethodKind::Method => PropVal::Method(f),
                        swc_ecma_ast::MethodKind::Getter => PropVal::Getter(f),
                        swc_ecma_ast::MethodKind::Setter => PropVal::Setter(f),
                    }=> &c.key));
                }
                ClassMember::PrivateProp(p) => {
                    members.push((
                        if p.is_static {
                            MemberFlags::STATIC
                        } else {
                            MemberFlags::empty()
                        },
                        PropKey::Lit(PropSym {
                            sym: p.key.name.clone(),
                            span: p.key.span,
                            ctx: PrivateKind::Private(
                                privates.get(&p.key.name).cloned().unwrap_or_default(),
                            ),
                        }),
                        PropVal::Item(match p.value.as_ref() {
                            None => None,
                            Some(a) => Some({
                                let b2;
                                (b2, t) = self.expr(o, t, a)?;
                                b2
                            }),
                        }),
                    ));
                }
                ClassMember::PrivateMethod(p) => {
                    let f =
                        TFunc::try_from_with_mapper(&(mapper.to_cfg)(&p.function)?, mapper.bud())?;
                    let x = match &p.kind {
                        swc_ecma_ast::MethodKind::Method => PropVal::Method(f),
                        swc_ecma_ast::MethodKind::Getter => PropVal::Getter(f),
                        swc_ecma_ast::MethodKind::Setter => PropVal::Setter(f),
                    };
                    members.push((
                        if p.is_static {
                            MemberFlags::STATIC
                        } else {
                            MemberFlags::empty()
                        },
                        PropKey::Lit(PropSym {
                            sym: p.key.name.clone(),
                            span: p.key.span,
                            ctx: PrivateKind::Private(
                                privates.get(&p.key.name).cloned().unwrap_or_default(),
                            ),
                        }),
                        x,
                    ));
                }
                _ => return Err(crate::Error::Unsupported { file: file!(), line: line!() }),
            }
        }
        let tmp = o.regs.alloc(());
        o.blocks[t].stmts.push(TStmt {
            left: LId::Id { id: tmp.clone() },
            flags: Default::default(),
            right: Item::Class(TClass {
                superclass,
                members,
                constructor,
            }),
            span: s.span(),
        });
        o.decls.insert(tmp.clone());
        Ok((tmp, t))
    }
    fn assign(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        tgt: &AssignTarget,
        op: &AssignOp,
        right: Ident,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        match tgt {
            swc_ecma_ast::AssignTarget::Simple(simple_assign_target) => match &simple_assign_target
            {
                SimpleAssignTarget::Ident(i) => {
                    let item = match (*op).to_update() {
                        None => Item::Just { id: right.clone() },
                        Some(a) => Item::Bin {
                            left: right.clone(),
                            right: i.id.clone().into(),
                            op: a,
                        },
                    };
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id {
                            id: i.id.clone().into(),
                        },
                        flags: Default::default(),
                        right: item,
                        span: i.span(),
                    });
                    // right = i.id.clone().into();
                }
                SimpleAssignTarget::Member(m) => {
                    let obj;
                    let mem;
                    let mut priv_ = None;
                    let mut private = false;
                    let e;
                    (obj, t) = self.expr(o, t, &m.obj)?;
                    'a: {
                        (mem, t) = self.expr(
                            o,
                            t,
                            match &m.prop {
                                swc_ecma_ast::MemberProp::Ident(ident_name) => {
                                    e = Expr::Ident(swc_ecma_ast::Ident::new(
                                        ident_name.sym.clone(),
                                        ident_name.span,
                                        Default::default(),
                                    ));
                                    &e
                                }
                                swc_ecma_ast::MemberProp::PrivateName(private_name) => {
                                    private = true;
                                    priv_ = Some(Private {
                                        sym: private_name.name.clone(),
                                        ctxt: self
                                            .mapper
                                            .privates
                                            .get(&private_name.name)
                                            .cloned()
                                            .unwrap_or_default(),
                                        span: private_name.span,
                                    });
                                    mem = match priv_.clone().unwrap() {
                                        Private {
                                            sym: a, ctxt: b, ..
                                        } => (a, b),
                                    };
                                    break 'a;
                                }
                                swc_ecma_ast::MemberProp::Computed(computed_prop_name) => {
                                    &computed_prop_name.expr
                                }
                            },
                        )?;
                    }
                    let item = match (*op).to_update() {
                        None => Item::Just { id: right.clone() },
                        Some(a) => {
                            let id = o.regs.alloc(());
                            o.blocks[t].stmts.push(TStmt {
                                left: LId::Id { id: id.clone() },
                                flags: ValFlags::SSA_LIKE,
                                right: if private {
                                    Item::PrivateMem {
                                        obj: obj.clone(),
                                        mem: priv_.as_ref().unwrap().clone(),
                                    }
                                } else {
                                    Item::Mem {
                                        obj: obj.clone(),
                                        mem: mem.clone(),
                                    }
                                },
                                span: m.span(),
                            });
                            Item::Bin {
                                left: right.clone(),
                                right: id,
                                op: a,
                            }
                        }
                    };
                    o.blocks[t].stmts.push(TStmt {
                        left: if private {
                            LId::Private {
                                obj: obj.clone(),
                                id: priv_.as_ref().unwrap().clone(),
                            }
                        } else {
                            LId::Member {
                                obj: obj.clone(),
                                mem: [mem.clone()],
                            }
                        },
                        flags: Default::default(),
                        right: item,
                        span: m.span(),
                    });
                    // right = o.regs.alloc(());
                    // o.blocks[t].stmts.push(TStmt {
                    //     left: LId::Id { id: right.clone() },
                    //     flags: ValFlags::SSA_LIKE,
                    //     right: Item::Mem { obj, mem },
                    //     span: m.span(),
                    // });
                    // o.decls.insert(right.clone());
                }
                _ => return Err(crate::Error::Unsupported { file: file!(), line: line!() }),
            },
            swc_ecma_ast::AssignTarget::Pat(assign_target_pat) => match &assign_target_pat {
                AssignTargetPat::Object(p) => {
                    t = self.bind_object(o, t, p, right.clone(), false)?;
                }
                AssignTargetPat::Array(p) => {
                    t = self.bind_array(o, t, p, right.clone(), false)?;
                }
                _ => return Err(crate::Error::Unsupported { file: file!(), line: line!() }),
            },
        };
        Ok((right, t))
    }
    fn frame(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        f: Frame<'_>,
        s: Ident,
        r: Ident,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        match f {
            Frame::Assign(assign_target, assign_op) => {
                self.assign(o, t, assign_target, &assign_op, s)
            }
            Frame::Member(m) => self.member_prop(o, t, m, s),
            Frame::Member2(a, b2) => {
                let mem;
                (mem, t) = self.convert_cond_prop(o, t, r, a, b2, Span::dummy_with_cmt())?;
                let v = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: v.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Mem { obj: s, mem },
                    span: Span::dummy_with_cmt(),
                });
                o.decls.insert(v.clone());
                Ok((v, t))
            }
            Frame::Call(a, b2) => {
                let mut args = Vec::default();
                let mut arg;
                for (a, b2) in a.iter().zip(b2.iter()) {
                    (arg, t) =
                        self.convert_cond_expr(o, t, r.clone(), a, b2, Span::dummy_with_cmt())?;
                    args.push(SpreadOr {
                        value: arg,
                        is_spread: false,
                    });
                }
                let v = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: v.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Call {
                        callee: TCallee::Val(s),
                        args,
                    },
                    span: Span::dummy_with_cmt(),
                });
                o.decls.insert(v.clone());
                Ok((v, t))
            }
            Frame::CallMember(prop, a, b2) => {
                let mem;
                (mem, t) = self.member_prop_expr(o, t, prop)?;
                let mut args = Vec::default();
                let mut arg;
                for (a, b2) in a.iter().zip(b2.iter()) {
                    (arg, t) =
                        self.convert_cond_expr(o, t, r.clone(), a, b2, Span::dummy_with_cmt())?;
                    args.push(SpreadOr {
                        value: arg,
                        is_spread: false,
                    });
                }
                let v = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: v.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Call {
                        callee: TCallee::Member {
                            func: s,
                            member: mem,
                        },
                        args,
                    },
                    span: Span::dummy_with_cmt(),
                });
                o.decls.insert(v.clone());
                Ok((v, t))
            }
            Frame::CallMember2(a, am, b2, bm) => {
                let mem;
                (mem, t) =
                    self.convert_cond_prop(o, t, r.clone(), am, bm, Span::dummy_with_cmt())?;
                let mut args = Vec::default();
                let mut arg;
                for (a, b2) in a.iter().zip(b2.iter()) {
                    (arg, t) =
                        self.convert_cond_expr(o, t, r.clone(), a, b2, Span::dummy_with_cmt())?;
                    args.push(SpreadOr {
                        value: arg,
                        is_spread: false,
                    });
                }
                let v = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: v.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Call {
                        callee: TCallee::Member {
                            func: s,
                            member: mem,
                        },
                        args,
                    },
                    span: Span::dummy_with_cmt(),
                });
                o.decls.insert(v.clone());
                Ok((v, t))
            }
            Frame::Await => {
                let v = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: v.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Await { value: s },
                    span: Span::dummy_with_cmt(),
                });
                o.decls.insert(v.clone());
                Ok((v, t))
            }
            Frame::Yield { delegate } => {
                let v = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: v.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Yield {
                        value: Some(s),
                        delegate,
                    },
                    span: Span::dummy_with_cmt(),
                });
                o.decls.insert(v.clone());
                Ok((v, t))
            }
            Frame::Cond {
                thena,
                elsea,
                fra,
                thenb,
                elseb,
                frb,
            } => {
                let mut a;
                let mut b2;
                (a, t) =
                    self.convert_cond_expr(o, t, s.clone(), thena, elsea, Span::dummy_with_cmt())?;
                for f in fra.into_iter() {
                    (a, t) = self.frame(o, t, f, a, s.clone())?;
                }
                (b2, t) =
                    self.convert_cond_expr(o, t, s.clone(), thenb, elseb, Span::dummy_with_cmt())?;
                for f in frb.into_iter() {
                    (b2, t) = self.frame(o, t, f, b2, s.clone())?;
                }
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Select {
                        cond: r.clone(),
                        then: a,
                        otherwise: b2,
                    },
                    span: Span::dummy_with_cmt(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
        }
    }
    fn inlinable(&self, x: &Expr) -> bool {
        match x {
            Expr::Fn(_) | Expr::Arrow(_) => true,
            _ => false,
        }
    }
    pub fn expr(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        s: &Expr,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        // if let Some(i2) = self.import_mapper[ImportMapperReq::Native].as_deref() {
        //     if let Some(n) = s.resolve_natives(i2) {
        //         let arg = n.map(&mut |e| {
        //             let x;
        //             (x, t) = self.expr(i, o, b, t, e)?;
        //             Ok(x)
        //         })?;
        //         let tmp = o.regs.alloc(());
        //         o.blocks[t].stmts.push(TStmt {
        //             left: LId::Id { id: tmp.clone() },
        //             flags: ValFlags::SSA_LIKE,
        //             right: Item::Intrinsic { value: arg },
        //             span: s.span(),
        //         });
        //         o.decls.insert(tmp.clone());
        //         return Ok((tmp, t));
        //     }
        // }
        match s {
            Expr::Class(c) => {
                let d;
                (d, t) = self.class(o, t, &c.class)?;
                if let Some(n) = c.ident.as_ref() {
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: n.to_id() },
                        flags: Default::default(),
                        right: Item::Just { id: d.clone() },
                        span: n.span(),
                    });
                }
                Ok((d, t))
            }
            Expr::Cond(c) => {
                let v;
                (v, t) = self.expr(o, t, &c.test)?;
                self.convert_cond_expr(o, t, v, &c.cons, &c.alt, c.span)
            }
            Expr::This(this) => {
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::This,
                    span: this.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Ident(id) => match self.mapper.consts.and_then(|c| c.map.get(&id.to_id())) {
                Some(e) if self.inlinable(e) => self.expr(o, t, &e.clone()),
                _ => match &*id.sym {
                    "arguments" => {
                        let tmp = o.regs.alloc(());
                        o.blocks[t].stmts.push(TStmt {
                            left: LId::Id { id: tmp.clone() },
                            flags: ValFlags::SSA_LIKE,
                            right: Item::Arguments,
                            span: id.span(),
                        });
                        o.decls.insert(tmp.clone());
                        Ok((tmp, t))
                    }
                    _ => Ok((id.clone().into(), t)),
                },
            },
            Expr::Assign(a) => {
                let right;
                (right, t) = self.expr(o, t, &a.right)?;
                let (right, t) = self.assign(o, t, &a.left, &a.op, right)?;
                Ok((right, t))
            }
            Expr::New(n) => {
                let obj;
                (obj, t) = self.expr(o, t, &n.callee)?;
                let args = n
                    .args
                    .iter()
                    .flatten()
                    .map(|a| {
                        let arg;
                        (arg, t) = self.expr(o, t, &a.expr)?;
                        Ok(arg)
                    })
                    .collect::<Result<_, crate::Error>>()?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::New { class: obj, args },
                    span: n.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Call(call) => {
                let (c, args, t2) = self.convert_call_expr(o, t, call)?;
                t = t2;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Call { callee: c, args },
                    span: call.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Bin(bin) => match (&*bin.left, &*bin.right, bin.op) {
                (Expr::PrivateName(p), obj, BinaryOp::In) => {
                    let o2;
                    (o2, t) = self.expr(o, t, obj)?;
                    let mem = Private {
                        sym: p.name.clone(),
                        ctxt: self
                            .mapper
                            .privates
                            .get(&p.name)
                            .cloned()
                            .unwrap_or_default(),
                        span: p.span,
                    };
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::HasPrivateMem { obj: o2, mem },
                        span: bin.span(),
                    });
                    o.decls.insert(tmp.clone());
                    Ok((tmp, t))
                }
                (Expr::Lit(Lit::Str(s)), obj, BinaryOp::In)
                    if self
                        .mapper
                        .semantic
                        .flags
                        .contains(SemanticFlags::PLUGIN_AS_TILDE_PLUGIN)
                        && s.value == "~plugin" =>
                {
                    let o2;
                    (o2, t) = self.expr(o, t, obj)?;
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Lit {
                            lit: Lit::Bool(Bool {
                                span: s.span,
                                value: false,
                            }),
                        },
                        span: bin.span(),
                    });
                    o.decls.insert(tmp.clone());
                    Ok((tmp, t))
                }
                (l, Expr::Lit(Lit::Num(Number { value: 0.0, .. })), BinaryOp::BitOr)
                | (Expr::Lit(Lit::Num(Number { value: 0.0, .. })), l, BinaryOp::BitOr) => {
                    let left;
                    // let right;
                    (left, t) = self.expr(o, t, l)?;
                    // (right, t) = self.expr(o, t, r)?;
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Asm {
                            value: Asm::OrZero(left),
                        },
                        span: bin.span(),
                    });
                    o.decls.insert(tmp.clone());
                    Ok((tmp, t))
                }
                (l, r, op) => {
                    let left;
                    let right;
                    (left, t) = self.expr(o, t, l)?;
                    (right, t) = self.expr(o, t, r)?;
                    if left == right
                        && self
                            .mapper
                            .semantic
                            .flags
                            .contains(SemanticFlags::BITWISE_OR_ABSENT_NAN)
                    {
                        match op {
                            BinaryOp::EqEqEq => {
                                let tmp = o.regs.alloc(());
                                o.blocks[t].stmts.push(TStmt {
                                    left: LId::Id { id: tmp.clone() },
                                    flags: ValFlags::SSA_LIKE,
                                    right: Item::Lit {
                                        lit: Lit::Bool(Bool {
                                            span: bin.span,
                                            value: true,
                                        }),
                                    },
                                    span: bin.span(),
                                });
                                o.decls.insert(tmp.clone());
                                return Ok((tmp, t));
                            }
                            BinaryOp::NotEqEq => {
                                let tmp = o.regs.alloc(());
                                o.blocks[t].stmts.push(TStmt {
                                    left: LId::Id { id: tmp.clone() },
                                    flags: ValFlags::SSA_LIKE,
                                    right: Item::Lit {
                                        lit: Lit::Bool(Bool {
                                            span: bin.span,
                                            value: false,
                                        }),
                                    },
                                    span: bin.span(),
                                });
                                o.decls.insert(tmp.clone());
                                return Ok((tmp, t));
                            }
                            _ => {}
                        }
                    }
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Bin { left, right, op },
                        span: bin.span(),
                    });
                    o.decls.insert(tmp.clone());
                    Ok((tmp, t))
                }
            },
            Expr::Unary(un) => {
                if un.op == UnaryOp::Void {
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Undef,
                        span: un.span(),
                    });
                    o.decls.insert(tmp.clone());
                    return Ok((tmp, t));
                }
                let arg;
                // let right;
                (arg, t) = self.expr(o, t, &un.arg)?;
                // (right, t) = self.expr(o, t, &bin.right)?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Un { arg, op: un.op },
                    span: un.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Member(m) => self.member_expr(o, t, m),
            Expr::Lit(l) => {
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Lit { lit: l.clone() },
                    span: l.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Fn(f) => {
                let tmp = match &f.ident {
                    Some(a) => a.clone().into(),
                    None => o.regs.alloc(()),
                };
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: Default::default(),
                    right: Item::Func {
                        func: TFunc::try_from_with_mapper(
                            &(self.mapper.to_cfg)(&f.function)?,
                            self.mapper.bud(),
                        )?,
                        arrow: false,
                    },
                    span: f.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Arrow(a) => {
                let mut c = swc_cfg::Func::default();
                c.is_generator = a.is_generator;
                c.is_async = a.is_async;
                c.params = a
                    .params
                    .iter()
                    .cloned()
                    .map(|a| Param {
                        span: a.span(),
                        decorators: vec![],
                        pat: a,
                    })
                    .collect();
                let k = swc_cfg::to_cfg::ToCfgConversionCtx::default();
                match a.body.as_ref() {
                    swc_ecma_ast::BlockStmtOrExpr::BlockStmt(block_stmt) => {
                        k.transform_all(
                            &mut c.cfg,
                            &mut (),
                            &block_stmt.stmts.clone(),
                            c.entry,
                            None,
                        )?;
                    }
                    swc_ecma_ast::BlockStmtOrExpr::Expr(expr) => {
                        c.cfg.blocks[c.entry].end = swc_cfg::End {
                            catch: swc_cfg::Catch::Throw,
                            orig_span: Some(a.span),
                            term: swc_cfg::Term::Return(Some(expr.as_ref().clone())),
                        }
                    }
                }
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: Default::default(),
                    right: Item::Func {
                        func: TFunc::try_from_with_mapper(&c, self.mapper.bud())?,
                        arrow: true,
                    },
                    span: a.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Array(arr) => {
                let members = arr
                    .elems
                    .iter()
                    .flat_map(|a| a.as_ref())
                    .map(|x| {
                        Ok({
                            let y;
                            (y, t) = self.expr(o, t, &x.expr)?;
                            SpreadOr {
                                value: y,
                                is_spread: x.spread.is_some(),
                            }
                        })
                    })
                    .collect::<Result<_, crate::Error>>()?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Arr { members },
                    span: arr.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Object(obj) => {
                let members = obj
                    .props
                    .iter()
                    .map(|a| {
                        macro_rules! prop_name {
                            ($v:expr => $a:expr) => {
                                match $v {
                                    v => match $a {
                                        swc_ecma_ast::PropName::Ident(ident_name) => Some((
                                            PropKey::Lit(PropSym {
                                                sym: ident_name.sym.clone(),
                                                span: ident_name.span,
                                                ctx: (),
                                            }),
                                            v,
                                        )),
                                        swc_ecma_ast::PropName::Str(s) => Some((
                                            PropKey::Lit(PropSym {
                                                sym: s.value.as_atom().cloned().unwrap(),
                                                span: s.span,
                                                ctx: (),
                                            }),
                                            v,
                                        )),
                                        swc_ecma_ast::PropName::Num(number) => {
                                            return Err(crate::Error::Unsupported { file: file!(), line: line!() })
                                        }
                                        swc_ecma_ast::PropName::Computed(computed_prop_name) => {
                                            let w;
                                            (w, t) = self.expr(o, t, &computed_prop_name.expr)?;
                                            Some((PropKey::Computed(w), v))
                                        }
                                        swc_ecma_ast::PropName::BigInt(big_int) => {
                                            return Err(crate::Error::Unsupported { file: file!(), line: line!() })
                                        }
                                    },
                                }
                            };
                        }
                        Ok(match a {
                            swc_ecma_ast::PropOrSpread::Spread(_spread_element) => {
                                return Err(crate::Error::Unsupported { file: file!(), line: line!() })
                            }
                            swc_ecma_ast::PropOrSpread::Prop(prop) => match prop.as_ref() {
                                swc_ecma_ast::Prop::Shorthand(ident) => Some((
                                    PropKey::Lit(PropSym {
                                        sym: ident.sym.clone(),
                                        span: ident.span,
                                        ctx: (),
                                    }),
                                    PropVal::Item(ident.clone().into()),
                                )),
                                swc_ecma_ast::Prop::KeyValue(key_value_prop) => {
                                    let v;
                                    (v, t) = self.expr(o, t, &key_value_prop.value)?;
                                    let v = PropVal::Item(v);
                                    prop_name!(v => &key_value_prop.key)
                                }
                                swc_ecma_ast::Prop::Assign(_assign_prop) => {
                                    return Err(crate::Error::Unsupported { file: file!(), line: line!() })
                                }
                                swc_ecma_ast::Prop::Getter(getter_prop) => {
                                    let v = PropVal::Getter({
                                        let mut c = swc_cfg::Func::default();
                                        let k = swc_cfg::to_cfg::ToCfgConversionCtx::default();
                                        let _k = k.transform_all(
                                            &mut c.cfg,
                                            &mut (),
                                            &getter_prop
                                                .body
                                                .as_ref()
                                                .ok_or(crate::Error::Unsupported { file: file!(), line: line!() })?
                                                .stmts
                                                .clone(),
                                            c.entry,
                                            None,
                                        )?;
                                        TFunc::try_from_with_mapper(&c, self.mapper.bud())?
                                    });
                                    prop_name!(v => &getter_prop.key)
                                }
                                swc_ecma_ast::Prop::Setter(setter_prop) => {
                                    let v = PropVal::Setter({
                                        let mut c = swc_cfg::Func::default();
                                        c.params.push(Param {
                                            span: setter_prop.span,
                                            decorators: vec![],
                                            pat: *setter_prop.param.clone(),
                                        });
                                        let k = swc_cfg::to_cfg::ToCfgConversionCtx::default();
                                        let _k = k.transform_all(
                                            &mut c.cfg,
                                            &mut (),
                                            &setter_prop
                                                .body
                                                .as_ref()
                                                .ok_or(crate::Error::Unsupported { file: file!(), line: line!() })?
                                                .stmts
                                                .clone(),
                                            c.entry,
                                            None,
                                        )?;
                                        TFunc::try_from_with_mapper(&c, self.mapper.bud())?
                                    });
                                    prop_name!(v => &setter_prop.key)
                                }
                                swc_ecma_ast::Prop::Method(method_prop) => {
                                    let v = PropVal::Method(TFunc::try_from_with_mapper(
                                        &(self.mapper.to_cfg)(&method_prop.function)?,
                                        self.mapper.bud(),
                                    )?);
                                    prop_name!(v => &method_prop.key)
                                }
                            },
                        })
                    })
                    .filter_map(|a| match a {
                        Ok(Some(a)) => Some(Ok(a)),
                        Ok(None) => None,
                        Err(e) => Some(Err(e)),
                    })
                    .collect::<Result<Vec<_>, crate::Error>>()?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Obj { members },
                    span: obj.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Await(x) => {
                let (a, t) = self.expr(o, t, &x.arg)?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Await { value: a.clone() },
                    span: x.span(),
                });
                Ok((tmp, t))
            }
            Expr::Yield(y) => {
                let y2 = match &y.arg {
                    None => None,
                    Some(a) => {
                        let b2;
                        (b2, t) = self.expr(o, t, a.as_ref())?;
                        Some(b2)
                    }
                };
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Yield {
                        value: y2,
                        delegate: y.delegate,
                    },
                    span: y.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            Expr::Seq(s) => {
                let mut r = None;
                for a in s.exprs.iter() {
                    let c;
                    (c, t) = self.expr(o, t, a)?;
                    r = Some(c)
                }
                Ok((r.ok_or(crate::Error::Unsupported { file: file!(), line: line!() })?, t))
            }
            Expr::MetaProp(m) => {
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Meta { prop: m.kind },
                    span: m.span(),
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            _ => return Err(crate::Error::Unsupported { file: file!(), line: line!() }),
        }
    }

    fn convert_cond_prop(
        &mut self,

        o: &mut TCfg,

        t: TBlockId,
        test: Ident,
        cons: &MemberProp,
        alt: &MemberProp,
        span: Span,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        match (cons, alt) {
            (MemberProp::Computed(cons), MemberProp::Computed(alt)) => {
                self.convert_cond_expr(o, t, test, &cons.expr, &alt.expr, span)
            }
            (MemberProp::Ident(a), MemberProp::Ident(b)) => {
                let [a, b] = [a, b].map(|v| {
                    let val = o.regs.alloc(());
                    o.decls.insert(val.clone());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: val.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Lit {
                            lit: Lit::Str(Str {
                                span: v.span,
                                value: v.sym.clone().into(),
                                raw: None,
                            }),
                        },
                        span,
                    });
                    val
                });
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Select {
                        cond: test.clone(),
                        then: a,
                        otherwise: b,
                    },
                    span,
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            (MemberProp::Computed(cons), alt) => {
                self.convert_cond_expr(o, t, test, &cons.expr, &imp(alt.clone()), span)
            }
            (cons, MemberProp::Computed(alt)) => {
                self.convert_cond_expr(o, t, test, &imp(cons.clone()), &alt.expr, span)
            }
            _ => todo!(),
        }
    }
    /// Converts a conditional expression (CondExpr) to TAC, factoring out test, cons, alt, and span.
    fn convert_cond_expr(
        &mut self,

        o: &mut TCfg,

        mut t: TBlockId,
        test: Ident,
        cons: &Expr,
        alt: &Expr,
        span: Span,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        let v = test;
        if let Some(Item::Lit { lit: Lit::Bool(b2) }) = o.def(LId::Id { id: v.clone() }) {
            let w;
            (w, t) = self.expr(o, t, if b2.value { cons } else { alt })?;
            return Ok((w, t));
        }
        fn try_get_frames<'a, 'b: 'a>(
            a: &'a Expr,
            b: &'b Expr,
        ) -> Option<(Vec<Frame<'a>>, &'a Expr, &'b Expr)> {
            if (a.is_pure() && b.is_pure()) || a.eq_ignore_span(b) {
                Some((vec![], a, b))
            } else {
                match (a, b) {
                    (Expr::Assign(a), Expr::Assign(b))
                        if a.left.eq_ignore_span(&b.left)
                            && a.left.as_simple().is_some_and(|s| s.is_ident())
                            && a.op == b.op =>
                    {
                        let (mut e, a2, b) = try_get_frames(&a.right, &b.right)?;
                        e.push(Frame::Assign(&a.left, a.op));
                        Some((e, a2, b))
                    }
                    (Expr::Member(a), Expr::Member(b)) if a.prop.eq_ignore_span(&b.prop) => {
                        let (mut e, a2, b) = try_get_frames(&a.obj, &b.obj)?;
                        e.push(Frame::Member(&a.prop));
                        Some((e, a2, b))
                    }
                    (Expr::Member(a), Expr::Member(b))
                        if !(a.prop.is_private_name() || b.prop.is_private_name()) =>
                    {
                        let (mut e, a2, b2) = try_get_frames(&a.obj, &b.obj)?;
                        e.push(Frame::Member2(&a.prop, &b.prop));
                        Some((e, a2, b2))
                    }
                    (Expr::Await(a), Expr::Await(b)) => {
                        let (mut e, a2, b2) = try_get_frames(&a.arg, &b.arg)?;
                        e.push(Frame::Await);
                        Some((e, a2, b2))
                    }
                    (Expr::Yield(a), Expr::Yield(b)) if a.delegate == b.delegate => {
                        let (mut e, a2, b2) = try_get_frames(a.arg.as_ref()?, b.arg.as_ref()?)?;
                        e.push(Frame::Yield {
                            delegate: a.delegate,
                        });
                        Some((e, a2, b2))
                    }
                    (Expr::Cond(a), Expr::Cond(b)) => {
                        let (mut e, a2, b2) = try_get_frames(&a.test, &b.test)?;
                        let (fra, thena, elsea) = try_get_frames(&a.cons, &a.alt)?;
                        let (frb, thenb, elseb) = try_get_frames(&b.cons, &b.alt)?;
                        e.push(Frame::Cond {
                            thena,
                            elsea,
                            fra,
                            thenb,
                            elseb,
                            frb,
                        });
                        Some((e, a2, b2))
                    }
                    (Expr::Call(a), Expr::Call(b)) if a.args.len() == b.args.len() => {
                        let (Callee::Expr(a2), Callee::Expr(b2)) = (&a.callee, &b.callee) else {
                            return None;
                        };
                        match (&**a2, &**b2) {
                            (Expr::Member(a2), Expr::Member(b2))
                                if a2.prop.eq_ignore_span(&b2.prop) =>
                            {
                                let (mut e, a2_, b2) = try_get_frames(&a2.obj, &b2.obj)?;
                                e.push(Frame::CallMember(
                                    &a2.prop,
                                    a.args.iter().map(|a| &*a.expr).collect(),
                                    b.args.iter().map(|a| &*a.expr).collect(),
                                ));
                                Some((e, a2_, b2))
                            }
                            (Expr::Member(aa), Expr::Member(bb))
                                if !aa.prop.is_private_name() && !bb.prop.is_private_name() =>
                            {
                                let (mut e, a2_, b2) = try_get_frames(&aa.obj, &bb.obj)?;
                                e.push(Frame::CallMember2(
                                    a.args.iter().map(|a| &*a.expr).collect(),
                                    &aa.prop,
                                    b.args.iter().map(|a| &*a.expr).collect(),
                                    &bb.prop,
                                ));
                                Some((e, a2_, b2))
                            }
                            (Expr::Member(_), _) | (_, Expr::Member(_)) => None,
                            (Expr::Ident(i), j) | (j, Expr::Ident(i))
                                if !i.optional
                                    && i.sym == "eval"
                                    && match j {
                                        Expr::Ident(j) => !j.eq_ignore_span(i),
                                        _ => true,
                                    } =>
                            {
                                None
                            }
                            (a2, b2) => {
                                let (mut e, a2, b2) = try_get_frames(a2, b2)?;
                                e.push(Frame::Call(
                                    a.args.iter().map(|a| &*a.expr).collect(),
                                    b.args.iter().map(|a| &*a.expr).collect(),
                                ));
                                Some((e, a2, b2))
                            }
                        }
                    }
                    _ => None,
                }
            }
        }
        if let Some((frames, c2, a2)) = try_get_frames(cons, alt) {
            let cons;
            let alt;
            (cons, t) = self.expr(o, t, c2)?;
            (alt, t) = self.expr(o, t, a2)?;
            let mut tmp = o.regs.alloc(());
            o.blocks[t].stmts.push(TStmt {
                left: LId::Id { id: tmp.clone() },
                flags: ValFlags::SSA_LIKE,
                right: Item::Select {
                    cond: v.clone(),
                    then: cons,
                    otherwise: alt,
                },
                span,
            });
            o.decls.insert(tmp.clone());
            for f in frames.into_iter() {
                (tmp, t) = self.frame(o, t, f, tmp, v.clone())?;
            }
            return Ok((tmp, t));
        };
        let then = o.blocks.alloc(TBlock {
            stmts: vec![],
            post: TPostecedent {
                catch: o.blocks[t].post.catch.clone(),
                term: Default::default(),
                orig_span: Some(span),
            },
        });
        let els = o.blocks.alloc(TBlock {
            stmts: vec![],
            post: TPostecedent {
                catch: o.blocks[t].post.catch.clone(),
                term: Default::default(),
                orig_span: Some(span),
            },
        });
        let done = o.blocks.alloc(TBlock {
            stmts: vec![],
            post: TPostecedent {
                catch: o.blocks[t].post.catch.clone(),
                term: Default::default(),
                orig_span: Some(span),
            },
        });
        o.blocks[t].post.term = TTerm::CondJmp {
            cond: v,
            if_true: then,
            if_false: els,
        };
        let tmp = o.regs.alloc(());
        o.decls.insert(tmp.clone());
        let (a, then) = self.expr(o, then, cons)?;
        o.blocks[then].stmts.push(TStmt {
            left: LId::Id { id: tmp.clone() },
            flags: ValFlags::SSA_LIKE,
            right: Item::Just { id: a },
            span,
        });
        o.blocks[then].post.term = TTerm::Jmp(done);
        let (a, els) = self.expr(o, els, alt)?;
        o.blocks[els].stmts.push(TStmt {
            left: LId::Id { id: tmp.clone() },
            flags: ValFlags::SSA_LIKE,
            right: Item::Just { id: a },
            span,
        });
        o.blocks[els].post.term = TTerm::Jmp(done);
        Ok((tmp, done))
    }
    // Converts a MemberProp to an Expr or literal, as needed
    fn member_prop_expr(
        &mut self,

        o: &mut TCfg,

        t: TBlockId,
        prop: &MemberProp,
    ) -> Result<(Ident, TBlockId), crate::Error> {
        match prop {
            MemberProp::Ident(ident_name) => {
                let lit = Lit::Str(Str {
                    span: ident_name.span,
                    value: ident_name.sym.clone().into(),
                    raw: None,
                });
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Lit { lit },
                    span: ident_name.span,
                });
                o.decls.insert(tmp.clone());
                Ok((tmp, t))
            }
            MemberProp::PrivateName(_private_name) => {
                // TODO: handle private names if needed
                return Err(crate::Error::Unsupported { file: file!(), line: line!() })
            }
            MemberProp::Computed(computed_prop_name) => {
                self.expr(o, t, &computed_prop_name.expr)
            }
        }
    }
    // Private helper for tail call conversion
}
pub mod live;
pub mod main;
