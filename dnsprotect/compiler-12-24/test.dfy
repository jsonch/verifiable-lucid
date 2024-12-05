// In the current version of the dafny compiler, 
// memcalcret gets carried all the way to rust through the dafny AST backend!
// but only if you have it in this witness form. 
// I think that's okay. 
// But I don't know if it will work with the current version or not. 
// Either way --- finally a way to identify memops!
// Also, if the user does not tag the function as 
// returning a memcalcret<..>, the verifier will complain! 
// PERFECT!
type memcalcret<t(0)> = x : t | true witness *


type memcalc<!t(0)> = (t, t) -> memcalcret<t>


function add(x : int, y : int) : memcalcret<int> {
    x + y
}

method apply<t(0)>(f: memcalc<t>, x : t, y : t) returns (z : t) {
    return f(x, y);
}

method main(x : int, y : int) {
    var v := apply(add, x, y);
    print(v);
}
