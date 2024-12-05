include "AST.dfy"
include "Dafny-utils.dfy"
include "LAST.dfy"


module {:extern "LucidPlugin"} LucidPlugin {
  import opened DAST
  import opened Std.Wrappers
  import opened DAST.Format
  import opened Std.Collections
  import PPrint
  import Visitors
  import opened LAST

  class PPrintLucid {

    static function TypeToString(typ : Type) : string {
      match typ {
        case Primitive(Int) => "int"
        case Primitive(Bool) => "bool"
        case UserDefined(ResolvedType(path, typeArgs, kind, attributes, properMethods, extendedTypes)) => 
          if path == [Ident.Ident(Name("ArrayMemops")), Ident.Ident(Name("ArrayVar"))] then 
            "Array.t<32>" // TODO: extract size from typeArg --> it should be "bits", "counter", or bool
          else if path == [Ident.Ident(Name("LucidProg")), Ident.Ident(Name("bits"))] then 
            "int<8>"
          else if path == [Ident.Ident(Name("LucidProg")), Ident.Ident(Name("counter"))] then 
            "int<32>"
          else "$$ERROR UNKNOWN USER DEFINED TYPE$$"
        case _ => "$$ERROR UNKNOWN TYPE&&"
      }
    }

    // a formal is a parameter (as far as I've seen)
    static function FormalToString(fml : Formal) : string 
    {
      TypeToString(fml.typ) + " " + fml.name.dafny_name
    }

    static function FormalsToString(fmls : seq<Formal>) : string 
    {
      PPrint.strFlatten(Seq.Map(FormalToString, fmls), ", ")
    }

    static function ExpressionToString(expr : Expression) : string 
    decreases expr
    {
      match expr {
        case Literal(BoolLiteral(b)) => 
          if b then "true" else "false"
        case Literal(IntLiteral(intstr, ty)) => intstr
        case Ident(name) => name.dafny_name
        case Call(on, callName, typeArgs, args) => 
          var fcn_name := match callName {
            case CallName(name, onType, recArgs, sig) => 
              name.dafny_name
            case _ => "$$ERROR UNKNOWN CALLNAME KIND&&"
          };
          var argStr := seq(|args|, i requires 0 <= i < |args| => ExpressionToString(args[i]));         
          fcn_name + "(" + PPrint.strFlatten(argStr, ", ") + ")"
        case _ => 
          "$$ERROR UNSUPPORTED EXPRESSION KIND$$"
      }
    }

    static function AssignLhsToString(lhs : AssignLhs) : string {
      match lhs {
        case Ident(id) => id.id.dafny_name
        // LIMITATION: records and nested datatypes are not 
        // supported, so the only expr in a Select should 
        // be a reference to the program itself.
        case Select(expr, field) => field.dafny_name 
        case Index => "$$INDEX LHS NOT SUPPORTED$$"
      }
    }

    static function DeclToString(decl : StrDecl) : string {
      match decl {
        // case Event(name, params) => "Event " + PPrint.nameToString(name) + "(" + PPrint.seqToString(params, PPrint.formalToString) + ");"
        case SDEvent(str) => str 
        case SDArray(str) => str
      }
    }

    static function ProgToString(decls : seq<StrDecl>) : string {
      PPrint.newline_sep(decls, DeclToString)
    }
  }

  // The compiler works in 3 phases.
  // 1. extract all the decls from the Dafny AST
  // 2. normalize AST nodes
  // 3. print Decls
  datatype Context = Context(
    decls : seq<StrDecl>,
    fields : seq<Field> // fields, which may be consts, globals, or symbolics
  )

  function attributeNames(attr : seq<Attribute>) : string {
    PPrint.comma_sep(attr, ((x : Attribute) => x.name))
  }

  function seqExists<T>(s : seq<T>, f : (T -> bool)) : bool {
    |Seq.Filter(f, s)| > 0
  }

  method printContext(ctx : Context) {
    print("--- Context ---\n");
    print("Decls:\n");
    var declstr := PPrintLucid.ProgToString(ctx.decls);
    print(declstr);
    print("\nFields:\n");
    var fieldnames := PPrint.newline_sep(ctx.fields, ((x : Field) => "{:" + attributeNames(x.formal.attributes) + "} " + x.formal.name.dafny_name));
    print(fieldnames);
    print("\n");
  }

  function internalFields(ctx: Context) : seq<Field> {
    Seq.Filter(fieldIsInternal, ctx.fields)
  }

  function fieldIsInternal(f : Field) : bool {
    seqExists (f.formal.attributes, ((x : Attribute) => x.name == "lucidInternal"))
  }



  class ExtractDecls {
    static const eventDatatypeName : Name  := Name("Event")
    static const progClassName : Name := Name("Program")


    static function extractEvent(dtc : DatatypeCtor) : StrDecl {
      var params := Seq.Map(
        ((x : DatatypeDtor) => x.formal), 
        dtc.args
      );
      var str := dtc.name.dafny_name + "(" + PPrintLucid.FormalsToString(params) + ");";
      SDEvent(str)
    }

    static function extractEvents(dt : Datatype) : seq<StrDecl> {
      Seq.Map(((x : DatatypeCtor) => extractEvent(x)), dt.ctors)
    }


    /* extract all the const variables from the program. 
        A method represents a const variable if it returns a literal.
        Problem: its impossible to distinguish between a const and a function that 
                 returns a const. Consts are literally turned into methods...?
    */
    // static function extractConstValue(body: seq<Statement>) : Option<Literal> {
    //   if |body| == 1 then 
    //     match body[0] {
    //       case Return(Literal(literal)) => 
    //         match literal {
    //           case IntLiteral(_, _) => Some(literal)
    //           case BoolLiteral(_) => Some(literal)
    //           case _ => None
    //         }
    //       case _ => None
    //     }
    //   else None
    // }
    static method extractConst(ctx:Context, m: Method) returns (result: Context) {
      // print ("[extractConst] " + m.name.dafny_name + "\n");
      // print ("------------------------------------------\n");
      // print (PPrint.methodToString(m));
      // print ("------------------------------------------\n");
      result := ctx;
    }

    // LEFT OFF HERE. What about consts? 
    // And we need to fix a few misc things: 
      // the "uniqueSig" parameter -- is it ghost? If not, what type is it?
      // arrays of booleans
      // array cell sizes


    /* Constructor translation. From the constructor, we derive the 
       global (Array) declarations. */

    // Expression simplifiers used in constructor
    static function simplifyConvert(expr : Expression) : Expression {
      match expr {
        case Convert(value, from, typ) => value
        case _ => expr
      }
    }
    static function simplifyArg(expr: Expression) : Expression {
      match expr {
        case Select(expr, field, isConstant, onDatatype, fieldType) => 
          Expression.Ident(field)
        case _ => expr
      }
    }
    static function simplifyArgs(expr: Expression) : Expression {
      match expr {
        case Call(on, callName, typeArgs, args) => 
          Expression.Call(on, callName, typeArgs, Seq.Map(simplifyArg, args))
        case _ => expr
      }
    }

    // strategy: for each DeclareVar(name: "_rhsX", maybeValue(Some(...))), 
    // stash name, string(expr) in the map. 
    // then, for each Assign(lhs = Select( ...), field = var), value = Ident(name = ...)
    // check for the name in the map and if it exists, emit it.  
    static function ConstrStatementToDecl(varmap: map<string, (Type, Expression)>, stmt : Statement) : (map<string, (Type, Expression)>, seq<StrDecl>) {
      match stmt {
        // if the constructor declares some intermediate variable, remember it
        case DeclareVar(name, typ, Some(val)) => 
          var namestr := name.dafny_name;
          (varmap + map[namestr := (typ, val)], [])
        // if the constructor assigns to a field, extract the field name from lhs, 
        // the field expr from rhs, and emit the entire declaration.
        case Assign(Select(this_exp, real_var_name), Ident(rhs_name)) => 
          if rhs_name.dafny_name in varmap then 
            var (typ, expr) := varmap[rhs_name.dafny_name];
            var decl_str := "global " + PPrintLucid.TypeToString(typ) + " " + real_var_name.dafny_name + " = Array." + PPrintLucid.ExpressionToString(expr) + ";";
            (varmap, [SDArray(decl_str)])
          else (varmap, [])
        case _ =>(varmap, [])
      }
    }
    static function ConstrStatementsToDecls(varmap: map<string, (Type, Expression)>, decls : seq<StrDecl>, stmts : seq<Statement>) : (map<string, (Type, Expression)>, seq<StrDecl>) 
    decreases stmts 
    {
      match |stmts| {        
        case 0 => (varmap, decls)
        case 1 => 
          var (new_varmap, new_decls) := ConstrStatementToDecl(varmap, stmts[0]);
          (new_varmap, decls + new_decls)
        case _ => 
          var (new_varmap, new_decls) := ConstrStatementToDecl(varmap, stmts[0]);
          var new_decls := decls + new_decls;
          ConstrStatementsToDecls(new_varmap, new_decls, stmts[1..])
      }
    }

    static method extractConstructor(ctx:Context, m:Method) returns (result: Context) {
      result := ctx;
      if (m.name.dafny_name == "__ctor") {
        var body := Visitors.exprInStatementsVisitor(m.body, simplifyConvert);
        body := Visitors.exprInStatementsVisitor(body, simplifyArgs);
        var (globalsMap, decls) := ConstrStatementsToDecls(map[], [], body);
        // print("------- global decls extracted from constructor ------\n");
        // var declStrs := Seq.Map(PPrintLucid.DeclToString, decls);
        // print (PPrint.strFlatten(declStrs, "\n"));
        // print ("-------------------------------------------------------\n");
        // print("------- constructor body ------\n");
        // print (PPrint.newline_sep(body, PPrint.statementToString));
        // print("\n");
        result := Context(result.decls + decls, result.fields);
      }
    }

    static method extractProgram(ctx: Context, c: Class) returns (result: Context) {
      result := ctx;
      // 1. record fields.
      result := Context(result.decls, result.fields + c.fields);
      printContext(result);
      // 2. extract consts, which may be used to construct global variables.
      for m:=0 to |c.body| {
        match c.body[m] {
          case Method(m) => result := extractConst(result, m);
        }
      }
      for m:=0 to |c.body| {
        match c.body[m] {
          case Method(m) => result := extractConstructor(result, m);
        }
      }
    }

    static method processModuleItems(ctx: Context, mis: seq<ModuleItem>) returns (result: Context) 
        decreases mis
    {
        var i := 0;
        result := ctx;
        while i < |mis| {
            var mi := mis[i];
            match mi {
                case Datatype(d) =>
                    if d.name == eventDatatypeName {
                        var eventDecls := extractEvents(d);
                        result := Context(result.decls + eventDecls, result.fields);
                    }
                case Class(c) =>
                    if c.name == progClassName {
                      result := extractProgram(result, c);
                    }
                case _ => result := ctx;
            }
            i := i + 1;
        }
    }

    static method processModule(ctx : Context, m : Module) returns (result: Context) {
      match m.body {
        case None => {result := ctx;}
        case Some(body) => {match |body| {
          case 0 => result := ctx;
          case _ => result := processModuleItems(ctx, body);
        }}
      }
    }

  }


  class COMP {
    
    static method Compile(p: seq<Module>) returns (s: string) {
      print("-------- program -----------\n");
      print(PPrint.modulesToString(p));
      print("\n-----------------------------\n");

      // var ctx := Context([], []);
      // var i := 0;
      // while i < |p| {
      //   var m := p[i];
      //   ctx := ExtractDecls.processModule(ctx, m);
      //   i := i + 1;
      // }
      s := PPrint.modulesToString(p);
      // s := PPrintLucid.ProgToString(ctx.decls);
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "";
    }

  }
}