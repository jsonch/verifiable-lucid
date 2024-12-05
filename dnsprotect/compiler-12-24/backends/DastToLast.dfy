include "AST.dfy"

include "LAST.dfy"
include "PPrintAst.dfy"
include "MapVisitor.dfy"
include "Analysis.dfy"

module Translator {
  import opened Std.Wrappers
  import opened Std.Collections


  import opened DAST
  import opened LAST
  import opened MapVisitor
  import Analysis
  import PPrint

  /* translators */
  datatype err = 
    | Base(msg:string)
    | Acc(msg:string, causes:seq<err>)

  function errStr(e:err) : string 
  decreases e, 0
  {
    match e {
      case Base(msg) => msg
      case Acc(msg, causes) => 
          msg + "(" + "\n" 
        + PPrint.indent(errStrs(causes)) + "\n"
        + ")"
    }
  }

  function errStrs(es:seq<err>) : string 
  decreases es, 1
  {
    // var argStr := seq(|args|, i requires 0 <= i < |args| => ExpressionToString(args[i]));         
    var strs := seq(|es|, i requires 0 <= i < |es| => errStr(es[i]));
    PPrint.newline_sep(strs, x => x)
  }

  datatype res<t> = 
    | Res(t)
    | Err(err)

  function baseErr<t>(msg:string) : res<t> {
    Err(Base(msg))
  }
  function accErr<t>(msg:string, causes:seq<err>) : res<t> {
    Err(Acc(msg, causes))
  }

  // names to idenfify program components
  const progClassName := Name("Program")
  const eventDatatypeName := Name("Event")
  // const dispatchMethodName := Name("dispatch")
  const ctorMethodName := Name("__ctor")

  // methods  and modules that don't get translated because they represent 
  // builtin mechanisms of the platform.
  const SkipModules := {
    Name("ArrayMemops"),
    Name("StateMemops"),
    Name("_module")
  }
  const SkipMethods := {
    Name("dispatch"),
    Name("simulateArrival"),
    Name("pickNextEvent"),
    Name("generateRecircEvent"),
    Name("simulatedClockTick"),
    Name("simulatedHardwareFailure")
  }

  // fully qualified names of types
  const progModuleIdent := Ident.Ident(Name("LucidProg"))

  const eventTyPath := [progModuleIdent, Ident.Ident(eventDatatypeName)]
  const recircCmdTyPath := [progModuleIdent, Ident.Ident(Name("RecircCmd"))]

  const arrayIdent := Ident.Ident(Name("ArrayMemops"))

  // special data structure types
  const arrayVarTyPath := [arrayIdent, Ident.Ident(Name("ArrayVar"))]
  const arrayTy := "Array.t"
  const boolArrayTy := "BoolArray.t"

  // primitive types
  const natTyPath := [Ident.Ident(Name("_System")), Ident.Ident(Name("nat"))]
  const intSz :nat := 32
  // TODO: parse "bits" and "counter" sizes from the program, 
  //       or force users to use some specific sized int types.
  const bitsTyPath := [progModuleIdent, Ident.Ident(Name("bits"))]
  const bitsSz :nat := 8
  const counterTyPath := [progModuleIdent, Ident.Ident(Name("counter"))]
  const counterSz := 32

  method trType(typ: Type) returns (r:res<ty>) {
    var typ_str := PPrint.typeToString(typ);
    match typ {
      case Primitive(Int) => {
        r := Res(TInt(intSz));
      }
      case Primitive(Bool) => {
        r := Res(TBool);
      }
      case UserDefined(ResolvedType(path, typeArgs, kind, attributes, properMethods, extendedTypes)) => {
        if path == arrayVarTyPath {
          if |typeArgs| == 1 {
              var cellTy := trType(typeArgs[0]);
              match cellTy {
                case Res(TBool) => {r := Res(TGlobal(boolArrayTy, NoTyArgs));}
                case Res(TInt(sz)) => {r := Res(TGlobal(arrayTy, Sizes([sz])));}
                case _ => {
                  print ("[trType]: unsupported cell type in array.\n");
                  r := baseErr("unsupported cell type in array");
                }
              }
          }
          else {
            print ("[trType]: wrong number of type args for array type.\n");
            r := baseErr("[trType]: wrong number of type args for array type.");
          }
        } else if (path == bitsTyPath) {
          r := Res(TInt(bitsSz));
        } else if (path == counterTyPath) {
          r := Res(TInt(counterSz));
        } else if (path == natTyPath) {
          r := Res(TInt(intSz));
        } else if (path == recircCmdTyPath) {
          r := Res(TDafnyGenerateCmd);
        } 
        else {
          print ("[trType]: unsupported type\n" + typ_str + "\n");
          r := baseErr("unsupported type");
        }
      }
      case typ => {
        print ("[trType]: unsupported type.\n");
        print ("-------------------------\n");
        print (PPrint.typeToString(typ));
        print ("\n-------------------------\n");
        r := baseErr("[trType]: unsupported type");
      }
    }        
  }
  method trTypes(typs: seq<Type>) returns (r:res<seq<ty>>) {
    var inner_rs := [];
    var errs := [];
    for i:=0 to |typs| {
      var tmp := trType(typs[i]);
      match tmp {
        case Res(ty) => {inner_rs := inner_rs + [ty];}
        case Err(e) => {errs := errs + [e];}
      }
    }
    if |errs| > 0 {
      r := accErr("[trTypes]", errs);
    } else {
      r := Res(inner_rs);
    }
  }

  method trTypeToSize(typ: Type) returns (r:res<nat>) {
    r := match typ {
      case Primitive(Int) => Res(intSz)
      case Primitive(Bool) => Res(8)
      case UserDefined(ResolvedType(path, typeArgs, kind, attributes, properMethods, extendedTypes)) => 
        if path == bitsTyPath then 
          Res(bitsSz)
        else if path == counterTyPath then
          Res(counterSz)
        else baseErr("[tyTypeToSize] unsupported type")
      case _ => baseErr("[tyTypeToSize] unsupported type")
    };
  }


  method trFormal(fml: Formal) returns (r:res<param>) {
    var ty := trType(fml.typ);
    match ty {
      case Err(s) => {
        print ("[trFormal]: error translating type\n");
        r :=  accErr("[trFormal]", [s]);} 
      case Res(ty) => {r := Res((fml.name.dafny_name, ty));}
    }
  }

  method trFormals(fmls: seq<Formal>) returns (r:res<seq<param>>) {
    var inner_rs := [];
    var errs := [];
    for i:=0 to |fmls| {
      var tmp := trFormal(fmls[i]);
      match tmp {
        case Res(p) => {inner_rs := inner_rs + [p];}
        case Err(e) => {errs := errs + [e];}
      }
    }
    if |errs| > 0 {
      r := accErr("[trFormals]", errs);
    } else {
      r := Res(inner_rs);
    }
  }

  // datatype op = 
  //   | Add | Sub
  //   | BitOr | BitAnd
  //   | Eq | Neq | Lt | Lte | Gt | Gte
  //   | Or | And | Neg | Not

  method trExpression(expr : Expression) returns (r: res<exp>) 
  decreases expr
  {
    var estr := PPrint.expressionToString(expr);
    var outstr := "\n[trExpression] current expr--------\n" + estr + "\n--------------------------------\n";
    match expr {
      case Literal(BoolLiteral(b)) => {r:= Res(EVal(VBool(b)));}
      case Literal(IntLiteral(str, typ)) => { 
        var s := trTypeToSize(typ);
        match s {
          case Res(s) => {
            r := Res(EVal(VInt(str, s)));
          }
          case Err(s) => {
            r := accErr("[trExpression.IntLiteral]", [s]);
          }
        }
      }
      case Ident(name) => {r:= Res(EVar(name.dafny_name));}
      case Call(on, callName, typeArgs, args) => {
        var name_prefix := "";
        match on {
          case Companion(idents, _) => {
            match |idents| {
              case 0 => {}
              case 1 => {
                  print("[trExpression] error: call with 1 ident\n");
                  print(outstr);
                  return baseErr("invalid 'on' in call");
              }
              case 2 => {
                if (idents[0] == arrayIdent) {
                  name_prefix := idents[0].id.dafny_name + ".";
                } else {
                  print ("[trExpression] error: call with 2 idents, but first one is not 'ArrayMemops'\n");
                  print(outstr);
                  return baseErr("[trExpression] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
                }
              }
              case _ => {
                  print("[trExpression] error: call with >2 idents\n");
                  print(outstr);
                  return baseErr("invalid 'on' in call");
              }
            }
          }
          case This() => {}
          case _ => {
            print ("[trExpression] unsupported feature: call with on that is not 'this' or 'ArrayMemops'\n");
            print(outstr);
            return baseErr("[trExpression] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
          }
        }
        match callName {
          case CallName(name, _, _, _) => {
            var args_rs := trExpressions(args);
            match args_rs {
              case Res(args_rs) => {
                r := Res(ECall(name_prefix + name.dafny_name, args_rs));
              }
              case Err(e) => {
                r := accErr("[trExpression.Call]", [e]);
              }
            }
          }
          //TODO: handle other cases
          case _ => {r := baseErr("[trExpression.Call] unsupported call name");}          
        }
      }
      case BinOp(binop, left, right, format2) => {
        // 1. figure out the op.
        var lucid_op : op;
        match binop {
          // the supported operations.
          case Plus => {lucid_op := Add;}
          case Minus => {lucid_op := Sub;}
          case BitwiseAnd => {lucid_op := BitAnd;}
          case BitwiseOr => {lucid_op := BitOr;}
          case BitwiseXor => {lucid_op := BitXor;}
          case BitwiseShiftLeft => {lucid_op := BitShiftL;}
          case BitwiseShiftRight => {lucid_op := BitShiftR;}
          case And => {lucid_op := op.And;}
          case Or => {lucid_op := op.Or;}
          case Eq(_) => {lucid_op := op.Eq;}
          case Lt => {lucid_op := op.Lt;}
          case Mod => {
            print("WARNING: Mod operation may not be translateable >>>>" + estr + "<<<<\n");
            lucid_op := op.DafnyMod;
          }
          case EuclidianMod => {
            print("WARNING: Mod operation may not be translateable >>>>" + estr + "<<<<\n");
            lucid_op := op.DafnyMod;
          }
          case Div => {
            print("WARNING: Divide operation may not be translateable >>>>" + estr + "<<<<\n");
            lucid_op := op.DafnyDiv;
          }
          case EuclidianDiv => {
            print("WARNING: Divide operation may not be translateable >>>>" + estr + "<<<<\n");
            lucid_op := op.DafnyDiv;
          }
          // the restof the operations will likely _never_ be supported
          // because they are about primitive types that lucid doesn't have.
          case _ => {
            print("[trExpression] unsupported op\n");
            print ("-----------\n");
            print (PPrint.expressionToString(expr));
            print ("\n-----------\n");
            r := baseErr("[trExpression] unsupported op");
            return r;
          }
        }
        // 2. translate the left and right expressions
        var left_exp := trExpression(left);
        var right_exp := trExpression(right);
        // 3. match the results
        match (left_exp, right_exp) {
          case (Res(left_exp), Res(right_exp)) => {
            r := Res(EOp(lucid_op, [left_exp, right_exp]));
          }
          case (Err(left_err), Res(_)) => {
            r := accErr("[trExpression] error translating left expression\n" + errStr(left_err), []);
          }
          case (Res(_), Err(right_err)) => {
            r := accErr("[trExpression] error translating right expression\n" + errStr(right_err), []);
          }
          case (Err(left_err), Err(right_err)) => {
            r := accErr("[trExpression] error translating left and right expressions\n" + errStr(left_err) + "\n" + errStr(right_err), []);
          }
        }
      }
      case UnOp(unop, expr, format1) => {
        var lucid_op : op;
        match unop {
          case Cardinality => {
            print("[trExpression] unsupported op: cardinality\n");
            r := baseErr("[trExpression] unsupported op: cardinality");
            return r;
          }
          case BitwiseNot => {
            print("[trExpression] unsupported op: bitwise not\n");
            r := baseErr("[trExpression] unsupported op: bitwise not");
            return r;
          }
          case Not => {lucid_op := op.Not;}
        }
        var exp := trExpression(expr);
        match exp {
          case Res(exp) => {
            r := Res(EOp(lucid_op, [exp]));
          }
          case Err(e) => {
            r := accErr("[trExpression] error translating expression\n" + errStr(e), []);
          }
        }
      }
      case DatatypeValue(dtt, typeArgs, variant, isCo, contents) => {
        // special case: a "recircCmd" that will later be translated 
        // into either a return (for a function) or a generate statement
        // (for a handler).
        if dtt.path == recircCmdTyPath {
          if (|typeArgs| > 0) {
            print("[trExpression] unsupported feature: datatype value with type args\n");
            r := baseErr("[trExpression] unsupported feature: datatype value with type args");
          } 
          else {            
            if (|contents| == 2) {
              var doit := trExpression(contents[0].1);
              var e := trExpression(contents[1].1);
              match (doit, e) {
                case (Res(doit), Res(e)) => {
                  r := Res(EDafnyGenerateCmd(doit, e));
                }
                case (Err(doit), Res(_)) => {
                  r := accErr("[trExpression] error translating doit\n" + errStr(doit), []);
                }
                case (Res(_), Err(e)) => {
                  r := accErr("[trExpression] error translating e\n" + errStr(e), []);
                }
                case (Err(doit), Err(e)) => {
                  r := accErr("[trExpression] error translating doit and e\n" + errStr(doit) + "\n" + errStr(e), []);
                }            
              }
            }
            else {
              print("[trExpression] unsupported feature: recircCmd with wrong number of args\n");
              r := baseErr("[trExpression] unsupported feature: recircCmd with wrong number of args");
            }
          }
        }
        // the only other datatype that is supported is the "event" datatype.
        else {
          if dtt.path == eventTyPath {
            if (|typeArgs| > 0) {
              print("[trExpression] unsupported feature: datatype value with type args\n");
              r := baseErr("[trExpression] unsupported feature: datatype value with type args");
            } 
            else {
              var args := [];
              var errs := [];              
              for i := 0 to |contents| {
                var tmp := trExpression(contents[i].1);
                match tmp {
                  case Res(arg) => {
                    args := args + [arg];
                  }
                  case Err(e) => {
                    errs := errs + [e];
                  }
                }
              }
              if |errs| > 0 {
                r := accErr("[trExpression]", errs);
              } else {
                r := Res(EEvent(variant.dafny_name, args));
              }
            }
          }
          else {
            print("[trExpression] unsupported feature: datatype value\n");
            r := baseErr("[trExpression] unsupported feature: datatype value");
          }
        }
        // var datatypeidents := datatypeType.path;
        // var datatypestrs := seq(|datatypeidents|, i requires 0 <= i < |datatypeidents| => datatypeidents[i].id.dafny_name);
        // var datatypestr := PPrint.comma_sep(datatypestrs, x => x);
        // print ("[trExpression] datatype: " + datatypestr + "\n");
        // r := baseErr("[trExpression] unsupported feature: datatype value");
      }
      case This() => {
        print "[trExpression] COMPILER ERROR: 'this' expressions cannot be translated directly \n";
        r := baseErr("[trExpression] COMPILER ERROR: 'this' expressions cannot be translated directly");
      }
      // ref to a constant or global
      case Select(This(), field, _, _, _) => {
        r := Res(EVar(field.dafny_name));
      }
      case SelectFn(This(), field, _, _, _) => {
        r := Res(EVar(field.dafny_name));
      }
      // special case: array helper
      case SelectFn(Companion(idents, _), field, _, _, _) => {
        if |idents| == 2 {
          if (idents[0] == arrayIdent) {
            var var_str := idents[0].id.dafny_name + "." + field.dafny_name;
            r := Res(EVar(var_str));
          } else {
            print("[trExpression] calling a function that belongs to a module besides builtin ArrayMemops\n");
            r := baseErr("[trExpression] calling a function that belongs to a module besides builtin ArrayMemops");
          }

        } else {
            print("[trExpression] calling a function that belongs to a module besides builtin ArrayMemops\n");
            r := baseErr("[trExpression] calling a function that belongs to a module besides builtin ArrayMemops");
        }
      }
      // case Ite(cond, thn, els) => {

      // }
      case _ => {
        print ("[trExpression]: unsupported expression type\n");
        print ("-------------------------\n");
        print (PPrint.expressionToString(expr));
        print ("\n-------------------------\n");
        r:= baseErr("[trExpression] unimplemented / supported expression type");
      }
    }
  }

  method trExpressions(exprs : seq<Expression>) returns (r: res<seq<exp>>) {
    var inner_rs := [];
    var errs := [];
    for i:=0 to |exprs| {
      var tmp := trExpression(exprs[i]);
      match tmp {
        case Res(e) => {inner_rs := inner_rs + [e];}
        case Err(e) => {
          errs := errs + [e];
        }
      }
    }
    if |errs| > 0 {
      r := accErr("[trExpressions]", errs);
    } else {
      r := Res(inner_rs);
    }
  }

  // translate a statement inside of a constructor
  type VarMap = map<string, (Type, Expression)>
  datatype StmtCtx = StmtCtx(vars : VarMap, stmts : seq<stmt>, decls : seq<decl>)
  method trConstrStatement(ctx : StmtCtx, stmt : Statement) 
    returns (outctx : StmtCtx)
    {
      var vars := ctx.vars;
      var stmts := ctx.stmts;
      var decls : seq<decl> := ctx.decls;
      match stmt {
        case DeclareVar(name, typ, Some(val)) => {
          vars := vars + map[name.dafny_name := (typ, val)];
        }
        case Assign(Select(this_exp, real_var_name), Ident(rhs_name)) => {
          if rhs_name.dafny_name in vars { 
            var (typ, expr) := vars[rhs_name.dafny_name];
            var ty := trType(typ);
            var ctor := trExpression(expr);
            match (ty, ctor) {
              case (Res(ty), Res(ctor)) => {
                var decl : decl := DGlobal(real_var_name.dafny_name, ty, ctor);
                decls := decls + [decl];
              }
              case (Err(ty_err), Res(_)) => {
                var decl : decl := DComment("[trConstrStatement] error translating type\n" + errStr(ty_err));
                decls := decls + [decl];
              }
              case (Res(_), Err(ctor_err)) => {
                var decl : decl := DComment("[trConstrStatement] error translating ctor\n" + errStr(ctor_err));
                decls := decls + [decl];
              }
              case (Err(ty_err), Err(ctor_err)) => {
                var decl : decl := DComment("[trConstrStatement] error translating type and ctor\n" + errStr(ty_err) + "\n" + errStr(ctor_err));
                decls := decls + [decl];
              }
            }
          }
        }
        case _ => {}
      }
      outctx := StmtCtx(vars, stmts, decls);
    }

    method trConstr(m:Method) returns (decls : seq<decl>)
    {
      print("      trConstr: " + m.name.dafny_name + "\n");
      var ctx := StmtCtx(map[], [], []);
      // transformations that we might want to do in a separate pass before translation
      var body := exprInStatementsVisitor(m.body, elimConvert);
      body := exprInStatementsVisitor(body, elimArgSelects);

      for i := 0 to |body| {
        ctx := trConstrStatement(ctx, body[i]);
      }
      return ctx.decls;
    }

    method printTrStmtErr(stmtStr : string, err : err) {
      print("[trStatement] error translating " + stmtStr + "\n");
      print(errStr(err));
      print ("\n-------------------\n");
    }

    method trStatement(s:Statement) returns (ls : res<seq<stmt>>) {
        var dbg_str := 
        "[trStatement] entering stmt--------\n" 
        + PPrint.statementToString(s) 
        + "\n--------------------------------\n";
        match s {
            case DeclareVar(name, typ, None) => {
                var ty := trType(typ);
                match ty {
                    case Res(ty) => {
                        return Res([DafnyDeclare(name.dafny_name, ty)]);
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating type\n" + errStr(e), []);
                    }
                }
            }
            case DeclareVar(name, typ, Some(InitializationValue(_))) => {
              var ty := trType(typ);
              match ty {
                case Res(ty) => {
                  return Res([DafnyDeclare(name.dafny_name, ty)]);
                }
                case Err(e) => {
                  printTrStmtErr(dbg_str, e);
                  return accErr("[trStatement] error translating type\n" + errStr(e), []);
                }
              }
            }
            case DeclareVar(name, typ, Some(This())) => {
              // if you assign "this" to an intermediate variable, it's a no-op.
              return Res([]);
            }
            case DeclareVar(name, typ, Some(val)) => {
                var ty := trType(typ);
                var exp := trExpression(val);
                match (ty, exp) {
                    case (Res(ty), Res(exp)) => {
                        return Res([SLocal(name.dafny_name, ty, exp)]);
                    }
                    case (Err(e), Res(_)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating type\n" + errStr(e), []);
                    }
                    case (Res(_), Err(e)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating expression\n" + errStr(e), []);
                    }
                    case (Err(ty_err), Err(e)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating type and expression\n" + errStr(ty_err) + "\n" + errStr(e), []);
                    }
                }
            }
            case Assign(Ident(lhs), rhs) => {
                var exp := trExpression(rhs);
                match exp {
                    case Res(exp) => {
                        return Res([SAssign(lhs.id.dafny_name, exp)]);
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating expression\n" + errStr(e), []);
                    }
                }
            }
            case Assign(Select(select_expr, field), rhs) => {
                var sstr := PPrint.statementToString(s);
                print("[trStatement] WARNING: field assignment. >>> " + sstr + "<<<.\n");
                var exp := trExpression(rhs);
                /* field assignments mean that we are updating an array variable. 
                   This is done internally in lucid, by the Array helpers. 
                   So we delete these nodes. */
                match exp {
                    case Res(exp) => {
                        return Res([SNoop]);
                        // return Res([SAssign(field.dafny_name, exp)]);
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating expression\n" + errStr(e), []);
                    }
                }
            }
            case Assign(Index(_, _), _) => {
                var e := Base("[trStatement] unsupported feature: array assignment");
                printTrStmtErr(dbg_str, e);
                return baseErr("[trStatement] unsupported feature: array assignment");
            }
            case If(cond, thn, els) => {
                var cond_exp := trExpression(cond);
                var thn_stmts := trStatements(thn);
                var els_stmts := trStatements(els);
                match (cond_exp, thn_stmts, els_stmts) {
                    case (Res(cond_exp), Res(thn_stmts), Res(els_stmts)) => {
                        return Res([SIf(cond_exp, thn_stmts, els_stmts)]);
                    }
                    case (Err(e), Res(_), Res(_)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating condition\n" + errStr(e), []);
                    }
                    case (Res(_), Err(e), Res(_)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating then branch\n" + errStr(e), []);
                    }
                    case (Res(_), Res(_), Err(e)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating else branch\n" + errStr(e), []);
                    }
                    case (Err(e1), Err(e2), Res(_)) => {
                        printTrStmtErr(dbg_str, e1);
                        return accErr("[trStatement] error translating condition and then branch\n" + errStr(e1) + "\n" + errStr(e2), []);
                    }
                    case (Err(e1), Res(_), Err(e2)) => {
                        printTrStmtErr(dbg_str, e1);
                        return accErr("[trStatement] error translating condition and else branch\n" + errStr(e1) + "\n" + errStr(e2), []);
                    }
                    case (Res(_), Err(e1), Err(e2)) => {
                        printTrStmtErr(dbg_str, e1);
                        return accErr("[trStatement] error translating then and else branches\n" + errStr(e1) + "\n" + errStr(e2), []);
                    }
                    case (Err(e1), Err(e2), Err(e3)) => {
                        printTrStmtErr(dbg_str, e1);
                        return accErr("[trStatement] error translating condition, then, and else branches\n" + errStr(e1) + "\n" + errStr(e2) + "\n" + errStr(e3), []);
                    }
                }                
            }
            case Labeled(_, stmts) => {
                var inner_rs := trStatements(stmts);
                return inner_rs;
            }
            case While(_, _) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: while loop"));
                return baseErr("[trStatement] unsupported feature: while loop");
            }
            case Foreach(_, _, _, _) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: foreach loop"));
                return baseErr("[trStatement] unsupported feature: foreach loop");
            }
            case Call(on, callName, typeArgs, args, outs) => {
                // assume that "on" is "this"
                // if (|typeArgs| > 0) {
                //     printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: call with type args"));
                //     return baseErr("[trStatement] unsupported feature: call with type args");
                // }
                var args_rs := trExpressions(args);
                var args_out := [];
                match args_rs {
                    case Res(args_rs) => {
                        args_out := args_rs;
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating call args\n" + errStr(e), []);
                    }
                }
                var outs_out := match outs {
                    case None => []
                    case Some(outs) => Seq.Map(((x : Ident) => x.id.dafny_name), outs)
                };
                var callName_out : string;
                match callName {
                    case CallName(name, _, _, _) => {
                        callName_out := name.dafny_name;
                    }
                    case _ => {
                        printTrStmtErr(dbg_str, Base("[trStatement] unsupported callName kind"));
                        return baseErr("[trStatement] unsupported callName kind.");
                    }
                }
                // add the prefix if there is one.
                match on {
                  case Companion(idents, _) => {
                    match |idents| {
                      case 0 => {}
                      case 2 => {
                        if (idents[0] == arrayIdent) {
                          callName_out := idents[0].id.dafny_name + "." + callName_out;
                        } else {
                          printTrStmtErr(dbg_str, Base("[trStatement] error: 2 idents, but first one is not 'ArrayMemops'"));
                          return baseErr("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
                        }
                      }
                      case _ => {
                        printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'"));
                        return baseErr("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
                      }
                    }
                  }
                  case This => {}
                  case _ => {
                    printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'"));
                    return baseErr("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
                  }
                }


                return Res([DafnyCall(callName_out, args_out, outs_out)]);
            }
            case Return(expr) => {
                var exp := trExpression(expr);
                match exp {
                    case Res(exp) => {
                        return Res([SRet(Some(exp))]);
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating expression\n" + errStr(e), []);
                    }
                }
            }
            case EarlyReturn() => {
                return Res([SRet(None)]);
            }
            case Break(_) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: break"));
                return baseErr("[trStatement] unsupported feature: break");
            }
            case TailRecursive(_) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: tail recursive"));
                return baseErr("[trStatement] unsupported feature: tail recursive");
            }
            case JumpTailCallStart() => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: jump tail call start"));
                return baseErr("[trStatement] unsupported feature: jump tail call start");
            }
            case Halt() => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: halt"));
                return baseErr("[trStatement] unsupported feature: halt");
            }
            case Print(exp) => {
                var strs := Analysis.getStringLiterals(exp);
                if |strs| == 1 {
                    return Res([SComment("print: " + strs[0])]);
                } else {
                    printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: print with 0 or multiple strings"));
                    return baseErr("[trStatement] unsupported feature: print with 0 or multiple strings");
                }
            }
            case ConstructorNewSeparator(_) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: constructor new separator"));
                return baseErr("[trStatement] unsupported feature: constructor new separator");
            }
        }
    }

    method trStatements(ss: seq<Statement>) returns (ls : res<seq<stmt>>) {
        var inner_rs := [];
        var errs := [];
        for i:=0 to |ss| {
            var tmp := trStatement(ss[i]);
            match tmp {
                case Res(s) => {inner_rs := inner_rs + s;}
                case Err(e) => {errs := errs + [e];}
            }
        }
        if |errs| > 0 {
            ls := accErr("[trStatements]", errs);
        } else {
            ls := Res(inner_rs);
        }
    }    

    method trMethod(m:Method) returns (decls : res<seq<decl>>) {
      if (m.name in SkipMethods) {
        print("      trMethod skipping " + m.name.dafny_name + "\n");
        return Res([]);
      }
      else {
        print("      trMethod translating " + m.name.dafny_name + "\n");
        if (|m.typeParams| > 0) {
          print("[trMethod] unsupported feature: method with type params");
          return baseErr("[trMethod] unsupported feature: method " + m.name.dafny_name + " has type params");
        } else {
          var params_res := trFormals(m.params);
          var params := [];
          match params_res {
            case Res(v) => {params := v;}
            case Err(e) => {
              print ("[trMethod] error translating params\n");
              return accErr("[trMethod] error translating params\n" + errStr(e), []);
            }
          }
          var rtys_res := trTypes(m.outTypes);
          var rtys := [];
          match rtys_res {
            case Res(v) => {rtys := v;}
            case Err(e) => {
              print ("[trMethod] error translating return types\n");
              return accErr("[trMethod] error translating return types\n" + errStr(e), []);
            }
          }
          var outvars := match m.outVars {
              case None => []
              case Some(outVars) => Seq.Map(((x : Ident) => x.id.dafny_name), outVars)
          };
          var mbody := exprInStatementsVisitor(m.body, elimConvert);
          mbody := exprInStatementsVisitor(mbody, elimArgSelects);
          var body_res := trStatements(mbody);
          var body := [];
          match body_res {
            case Res(v) => { body := v; }
            case Err(e) => {
              print ("[trMethod] error translating body\n");
              return accErr("[trMethod] error translating body\n" + errStr(e), []);
            }
          }
          var dout := DDafnyMethod(m.name.dafny_name, rtys, params, body, outvars);
          decls := Res([dout]);

          // if (m.name.dafny_name == "Q") || (m.name.dafny_name == "A") {
          //   print ("-----[trMethod] debug: Q method-----\n");
          //   var methodStr := PPrint.methodToString(m);
          //   print(methodStr);
          //   print ("------------------------------------\n");
          //   var doutStr := LAST.declStr(dout);
          //   print(doutStr);
          //   print ("------------------------------------\n");
          // }

        }
      }
    }


    method trMethodOuter(m:Method) returns (decls : seq<decl>)
    {
      // the constructor gets translated to declarations 
      // instead of statements
      if (m.name == ctorMethodName) {
        decls := trConstr(m);
      } else {
        var lucidDecl := trMethod(m);
        match lucidDecl {
          case Res(ds) => decls := ds;
          case Err(e) => {
            print ("[trMethodOrConstr] error translating method\n");
            decls := [DComment("error translating method\n" + errStr(e))];
          }
        }
      }
    }

    method trClass(c:Class) returns (decls : seq<decl>)
    {
      if c.name != progClassName {
        print("    trClass: skipping " + c.name.dafny_name + "\n");
        return [];
      }      
      else {
        print("    trClass: translating " + c.name.dafny_name + "\n");
        var fieldIds : seq<string> := [];
        for i := 0 to |c.fields| {
          fieldIds := fieldIds + [c.fields[i].formal.name.dafny_name];
          // print(c.fields[i].formal.name.dafny_name + " ");
        }
        var fieldOrderDecl := DDafnyFieldOrder(fieldIds);
        print("\n");
        decls := [fieldOrderDecl];
        for i:=0 to |c.body| {
          match c.body[i] {
            case Method(m) => {
              var new_decls := trMethodOuter(m);
              decls := decls + new_decls;
            }
          }
        }
      }
    }

    method trDatatypeCtor(c:DatatypeCtor) returns (decl : decl)
    {
      print ("    trDatatypeCtor: translating " + c.name.dafny_name + "\n");
      var params := [];
      var errs := [];
      for i := 0 to |c.args| {
        match c.args[i] {
          case DatatypeDtor(formal, _) => {
            var param := trFormal(formal);
            match param {
              case Res(param) => params := params + [param];
              case Err(err) => errs := errs + [err];
            }
          }
        }
      }
      if |errs| > 0 {
        print ("    trDatatypeCtor: error in datatype args\n");
        var ctorStr := PPrint.datatypeCtorToString(c);
        print ("    trDatatypeCtor: " + ctorStr + "\n");
        decl := DComment(ctorStr + " " + errStrs(errs));
      } else {
        decl := DEvent(c.name.dafny_name, params);
      }
    }

    method trDatatype(d:Datatype) returns (decls : seq<decl>)
    {
      if d.name != eventDatatypeName {
      print("  trDatatype: skipping " + d.name.dafny_name + "\n");
        return [];
      }
      else {       
        print("  trDatatype: translating " + d.name.dafny_name + "\n");
        decls := [];
        for i := 0 to |d.ctors| {
          var decl := trDatatypeCtor(d.ctors[i]);
          decls := decls + [decl];
        }
      }
    }


    method trModule(m : Module) returns (decls : seq<decl>)
    {
      // print(PPrint.moduleToString(m));
      // print("\n");
      if m.name in SkipModules {
        print ("trModule: skipping " + m.name.dafny_name + "\n");
        return [];
      } else {
        print ("trModule: translating  " + m.name.dafny_name + "\n");
        decls := [];
        match m.body {
          case None => return [];
          case Some(body) => {
            for i := 0 to |body| {
              match (body[i]) {
                case Class(c) => {
                  var newdecls := trClass(c);
                  decls := decls + newdecls;
                }
                case Datatype(d) => {
                  var newdecls := trDatatype(d);
                  decls := decls + newdecls;
                }
                case _ => {}
              }
            }
          }
        }
      }
    }

    method trModules(ms : seq<Module>) returns (decls : seq<decl>)
    {
      decls := [];
      for i := 0 to |ms| {
        var newdecls := trModule(ms[i]);
        var istr := PPrint.natToString(i);
        var num_decls := |newdecls|;
        var numdeclsstr := PPrint.natToString(num_decls);
        decls := decls + newdecls;
      }
    }
  
}