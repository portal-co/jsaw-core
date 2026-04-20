function classify(n) {
    if (n < 0) return "negative";
    if (n === 0) return "zero";
    return "positive";
}
console.log(classify(-5));
console.log(classify(0));
console.log(classify(3));
var label = 42 > 10 ? "big" : "small";
console.log(label);
