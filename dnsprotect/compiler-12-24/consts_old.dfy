
abstract module LBase {

  type {:extern "shit"} MemVal<t> 

}

module LucidProg {


  // type ConstVar<t> = t
  // function {:extern} {:axiom} Const<t>(x : t) : ConstVar<t> {
  //   x
  // }

  // datatype Tag = Tag

  // type {:extern "QQQ"} Q<t(!new)> = x : t | x > 0 witness 1

  // datatype Foo<T> = Foo(x : T)

  // type MemVal<T(!new, 0)> = x: T | true ghost witness var x: T :| true; x
  
  // Foo(var x: T :| true; x)


  // type MemVal<t, y> = t
  // now memops...

  // lemma {:axiom} MemValEssence<t>()
  //   ensures forall x : MemVal<t> :: x == (x as t)


  // type {:nativeType "uint"} uint32 = x | 0 <= x < 0x8000_0000

  // type {:nativeType "uint_const"} Const<t> = t

  newtype memval = nat



  class CLS {

    // const AConst : nat := Const(123)
    function {:compile} myop(x : memval) : memval {

      x
    }

    method helper(f : memval -> memval, arg : nat) returns (rv : nat) {
      return f(arg as memval) as nat;
    }

    method user(z : nat) returns (y : nat) {
      y:= helper(myop, z);
    }

    // function AFun() : int {
    //     666
    // }

    // method ConstUser() returns (x : int) {
    //     return AConst;
    // }
    // method FunUser() returns (x: int) {
    //     return AFun();
    // }

  }


}