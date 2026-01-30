package rise.eqsat

import rise.core.types.{DataType => rcdt}
import rise.core.semantics._

class SExprParserCheck extends test_util.Tests {
  import SExprParser._

  // Helper to check round-trip: parse then serialize should give equivalent result
  def roundTrip(input: String): Unit = {
    val expr = parse(input)
    val pattern = Pattern.fromExpr(expr)
    Reggvolution.anyCounter = 0
    val reserialized = Reggvolution.reggvolve(pattern)
    // Note: exact string match may not work due to whitespace/formatting differences
    // but the parsed structure should be equivalent
    val reparsed = parse(reserialized)
    assert(expr == reparsed, s"Round-trip failed:\nInput: $input\nReserialized: $reserialized")
  }

  // ==================== Basic S-expression parsing ====================

  test("parse simple atom") {
    val (atom, rest) = SExprParser.parseAtom("hello world")
    assert(atom == SAtom("hello"))
    assert(rest == " world")
  }

  test("parse simple list") {
    val sexpr = SExprParser.parseSExpr("(foo bar baz)")
    assert(sexpr == SList(Seq(SAtom("foo"), SAtom("bar"), SAtom("baz"))))
  }

  test("parse nested list") {
    val sexpr = SExprParser.parseSExpr("(foo (bar baz) qux)")
    assert(
      sexpr == SList(
        Seq(
          SAtom("foo"),
          SList(Seq(SAtom("bar"), SAtom("baz"))),
          SAtom("qux")
        )
      )
    )
  }

  // ==================== Variable parsing ====================

  test("parse expression variable $e0") {
    val expr = parse("(typeOf $e0 f32)")
    assert(expr.node == Var(0))
    assert(expr.t == Type(ScalarType(rcdt.f32)))
  }

  test("parse expression variable $e5") {
    val expr = parse("(typeOf $e5 i32)")
    assert(expr.node == Var(5))
    assert(expr.t == Type(ScalarType(rcdt.i32)))
  }

  // ==================== Literal parsing ====================

  test("parse integer literal") {
    val expr = parse("(typeOf 42i i32)")
    assert(expr.node == Literal(IntData(42)))
  }

  test("parse negative integer literal") {
    val expr = parse("(typeOf -7i i32)")
    assert(expr.node == Literal(IntData(-7)))
  }

  test("parse float literal with decimal") {
    val expr = parse("(typeOf 3.14 f32)")
    expr.node match {
      case Literal(FloatData(v)) => assert(math.abs(v - 3.14f) < 0.001f)
      case other                 => fail(s"Expected FloatData, got $other")
    }
  }

  test("parse float literal 0.0") {
    val expr = parse("(typeOf 0.0 f32)")
    expr.node match {
      case Literal(FloatData(v)) => assert(v == 0.0f)
      case other                 => fail(s"Expected FloatData(0.0), got $other")
    }
  }

  test("parse boolean true") {
    val expr = parse("(typeOf true bool)")
    assert(expr.node == Literal(BoolData(true)))
  }

  test("parse boolean false") {
    val expr = parse("(typeOf false bool)")
    assert(expr.node == Literal(BoolData(false)))
  }

  // ==================== NatLiteral parsing ====================

  test("parse nat literal in expression position") {
    val expr = parse("(typeOf 5n natT)")
    expr.node match {
      case NatLiteral(n) => assert(n == Nat(NatCst(5)))
      case other         => fail(s"Expected NatLiteral, got $other")
    }
  }

  test("parse nat var in expression position") {
    val expr = parse("(typeOf $n0 natT)")
    expr.node match {
      case NatLiteral(n) => assert(n == Nat(NatVar(0)))
      case other         => fail(s"Expected NatLiteral with NatVar, got $other")
    }
  }

  // ==================== Primitive parsing ====================

  test("parse map primitive") {
    val expr = parse("(typeOf map (fun (fun f32 f32) (fun (arrT 10n f32) (arrT 10n f32))))")
    expr.node match {
      case Primitive(p) => assert(p.name == "map")
      case other        => fail(s"Expected Primitive(map), got $other")
    }
  }

  test("parse reduce primitive") {
    val expr =
      parse("(typeOf reduce (fun (fun f32 (fun f32 f32)) (fun f32 (fun (arrT 10n f32) f32))))")
    expr.node match {
      case Primitive(p) => assert(p.name == "reduce")
      case other        => fail(s"Expected Primitive(reduce), got $other")
    }
  }

  test("parse add primitive") {
    val expr = parse("(typeOf add (fun f32 (fun f32 f32)))")
    expr.node match {
      case Primitive(p) => assert(p.name == "add")
      case other        => fail(s"Expected Primitive(add), got $other")
    }
  }

  // ==================== Lambda parsing ====================

  test("parse simple lambda") {
    val expr = parse("(typeOf (lam (typeOf $e0 f32)) (fun f32 f32))")
    expr.node match {
      case Lambda(body) =>
        assert(body.node == Var(0))
        assert(body.t == Type(ScalarType(rcdt.f32)))
      case other => fail(s"Expected Lambda, got $other")
    }
  }

  test("parse nested lambda") {
    val expr =
      parse("(typeOf (lam (typeOf (lam (typeOf $e0 f32)) (fun f32 f32))) (fun i32 (fun f32 f32)))")
    expr.node match {
      case Lambda(inner) =>
        inner.node match {
          case Lambda(body) => assert(body.node == Var(0))
          case other        => fail(s"Expected inner Lambda, got $other")
        }
      case other => fail(s"Expected outer Lambda, got $other")
    }
  }

  // ==================== Application parsing ====================

  test("parse simple application") {
    val expr = parse("(typeOf (app (typeOf id (fun f32 f32)) (typeOf $e0 f32)) f32)")
    expr.node match {
      case App(f, e) =>
        f.node match {
          case Primitive(p) => assert(p.name == "id")
          case other        => fail(s"Expected Primitive(id), got $other")
        }
        assert(e.node == Var(0))
      case other => fail(s"Expected App, got $other")
    }
  }

  // ==================== Nat lambda/app parsing ====================

  test("parse natLam") {
    val expr = parse("(typeOf (natLam (typeOf $e0 (arrT $n0 f32))) (natFun (arrT $n0 f32)))")
    expr.node match {
      case NatLambda(body) =>
        body.t match {
          case Type(ArrayType(n, et)) =>
            assert(n == Nat(NatVar(0)))
          case other => fail(s"Expected ArrayType, got $other")
        }
      case other => fail(s"Expected NatLambda, got $other")
    }
  }

  test("parse natApp") {
    val expr = parse("(typeOf (natApp (typeOf $e0 (natFun f32)) 5n) f32)")
    expr.node match {
      case NatApp(f, x) =>
        assert(f.node == Var(0))
        assert(x == Nat(NatCst(5)))
      case other => fail(s"Expected NatApp, got $other")
    }
  }

  // ==================== Data lambda/app parsing ====================

  test("parse dataLam") {
    val expr = parse("(typeOf (dataLam (typeOf $e0 $d0)) (dataFun $d0))")
    expr.node match {
      case DataLambda(body) =>
        body.t match {
          case Type(DataTypeVar(0)) => // ok
          case other                => fail(s"Expected DataTypeVar(0), got $other")
        }
      case other => fail(s"Expected DataLambda, got $other")
    }
  }

  test("parse dataApp") {
    val expr = parse("(typeOf (dataApp (typeOf $e0 (dataFun f32)) f32) f32)")
    expr.node match {
      case DataApp(f, dt) =>
        assert(f.node == Var(0))
        assert(dt == DataType(ScalarType(rcdt.f32)))
      case other => fail(s"Expected DataApp, got $other")
    }
  }

  // ==================== Address lambda/app parsing ====================

  test("parse addrLam") {
    val expr = parse("(typeOf (addrLam (typeOf $e0 f32)) (addrFun f32))")
    expr.node match {
      case AddrLambda(body) => assert(body.node == Var(0))
      case other            => fail(s"Expected AddrLambda, got $other")
    }
  }

  test("parse addrApp with global") {
    val expr = parse("(typeOf (addrApp (typeOf $e0 (addrFun f32)) global) f32)")
    expr.node match {
      case AddrApp(f, addr) =>
        assert(f.node == Var(0))
        assert(addr == Global)
      case other => fail(s"Expected AddrApp, got $other")
    }
  }

  test("parse addrApp with local") {
    val expr = parse("(typeOf (addrApp (typeOf $e0 (addrFun f32)) local) f32)")
    expr.node match {
      case AddrApp(_, addr) => assert(addr == Local)
      case other            => fail(s"Expected AddrApp with Local, got $other")
    }
  }

  test("parse addrApp with private") {
    val expr = parse("(typeOf (addrApp (typeOf $e0 (addrFun f32)) private) f32)")
    expr.node match {
      case AddrApp(_, addr) => assert(addr == Private)
      case other            => fail(s"Expected AddrApp with Private, got $other")
    }
  }

  test("parse addrApp with constant") {
    val expr = parse("(typeOf (addrApp (typeOf $e0 (addrFun f32)) constant) f32)")
    expr.node match {
      case AddrApp(_, addr) => assert(addr == Constant)
      case other            => fail(s"Expected AddrApp with Constant, got $other")
    }
  }

  test("parse address var") {
    val expr = parse("(typeOf (addrApp (typeOf $e0 (addrFun f32)) $a0) f32)")
    expr.node match {
      case AddrApp(_, addr) => assert(addr == AddressVar(0))
      case other            => fail(s"Expected AddrApp with AddressVar, got $other")
    }
  }

  // ==================== Type parsing ====================

  test("parse scalar types") {
    assert(parseType(SAtom("f32")) == Type(ScalarType(rcdt.f32)))
    assert(parseType(SAtom("f64")) == Type(ScalarType(rcdt.f64)))
    assert(parseType(SAtom("i32")) == Type(ScalarType(rcdt.i32)))
    assert(parseType(SAtom("i64")) == Type(ScalarType(rcdt.i64)))
    assert(parseType(SAtom("bool")) == Type(ScalarType(rcdt.bool)))
    assert(parseType(SAtom("int")) == Type(ScalarType(rcdt.int)))
  }

  test("parse function type") {
    val ty = parseType(SExprParser.parseSExpr("(fun f32 i32)"))
    ty match {
      case Type(FunType(inT, outT)) =>
        assert(inT == Type(ScalarType(rcdt.f32)))
        assert(outT == Type(ScalarType(rcdt.i32)))
      case other => fail(s"Expected FunType, got $other")
    }
  }

  test("parse nested function type") {
    val ty = parseType(SExprParser.parseSExpr("(fun f32 (fun i32 bool))"))
    ty match {
      case Type(FunType(inT, Type(FunType(inT2, outT2)))) =>
        assert(inT == Type(ScalarType(rcdt.f32)))
        assert(inT2 == Type(ScalarType(rcdt.i32)))
        assert(outT2 == Type(ScalarType(rcdt.bool)))
      case other => fail(s"Expected nested FunType, got $other")
    }
  }

  test("parse array type") {
    val ty = parseType(SExprParser.parseSExpr("(arrT 10n f32)"))
    ty match {
      case Type(ArrayType(n, et)) =>
        assert(n == Nat(NatCst(10)))
        assert(et == DataType(ScalarType(rcdt.f32)))
      case other => fail(s"Expected ArrayType, got $other")
    }
  }

  test("parse array type with nat var") {
    val ty = parseType(SExprParser.parseSExpr("(arrT $n0 f32)"))
    ty match {
      case Type(ArrayType(n, et)) =>
        assert(n == Nat(NatVar(0)))
      case other => fail(s"Expected ArrayType with NatVar, got $other")
    }
  }

  test("parse pair type") {
    val ty = parseType(SExprParser.parseSExpr("(pairT f32 i32)"))
    ty match {
      case Type(PairType(dt1, dt2)) =>
        assert(dt1 == DataType(ScalarType(rcdt.f32)))
        assert(dt2 == DataType(ScalarType(rcdt.i32)))
      case other => fail(s"Expected PairType, got $other")
    }
  }

  test("parse vector type") {
    val ty = parseType(SExprParser.parseSExpr("(vecT 4n f32)"))
    ty match {
      case Type(VectorType(n, et)) =>
        assert(n == Nat(NatCst(4)))
        assert(et == DataType(ScalarType(rcdt.f32)))
      case other => fail(s"Expected VectorType, got $other")
    }
  }

  test("parse index type") {
    val ty = parseType(SExprParser.parseSExpr("(idxT 10n)"))
    ty match {
      case Type(IndexType(n)) =>
        assert(n == Nat(NatCst(10)))
      case other => fail(s"Expected IndexType, got $other")
    }
  }

  test("parse natFun type") {
    val ty = parseType(SExprParser.parseSExpr("(natFun f32)"))
    ty match {
      case Type(NatFunType(t)) =>
        assert(t == Type(ScalarType(rcdt.f32)))
      case other => fail(s"Expected NatFunType, got $other")
    }
  }

  test("parse dataFun type") {
    val ty = parseType(SExprParser.parseSExpr("(dataFun f32)"))
    ty match {
      case Type(DataFunType(t)) =>
        assert(t == Type(ScalarType(rcdt.f32)))
      case other => fail(s"Expected DataFunType, got $other")
    }
  }

  // ==================== Nat parsing ====================

  test("parse nat constant") {
    val n = parseNat(SAtom("42n"))
    assert(n == Nat(NatCst(42)))
  }

  test("parse nat var") {
    val n = parseNat(SAtom("$n3"))
    assert(n == Nat(NatVar(3)))
  }

  test("parse natAdd") {
    val n = parseNat(SExprParser.parseSExpr("(natAdd 3n 5n)"))
    n match {
      case Nat(NatAdd(a, b)) =>
        assert(a == Nat(NatCst(3)))
        assert(b == Nat(NatCst(5)))
      case other => fail(s"Expected NatAdd, got $other")
    }
  }

  test("parse natMul") {
    val n = parseNat(SExprParser.parseSExpr("(natMul $n0 2n)"))
    n match {
      case Nat(NatMul(a, b)) =>
        assert(a == Nat(NatVar(0)))
        assert(b == Nat(NatCst(2)))
      case other => fail(s"Expected NatMul, got $other")
    }
  }

  test("parse natPow") {
    val n = parseNat(SExprParser.parseSExpr("(natPow 2n 3n)"))
    n match {
      case Nat(NatPow(base, exp)) =>
        assert(base == Nat(NatCst(2)))
        assert(exp == Nat(NatCst(3)))
      case other => fail(s"Expected NatPow, got $other")
    }
  }

  test("parse natMod") {
    val n = parseNat(SExprParser.parseSExpr("(natMod 10n 3n)"))
    n match {
      case Nat(NatMod(a, b)) =>
        assert(a == Nat(NatCst(10)))
        assert(b == Nat(NatCst(3)))
      case other => fail(s"Expected NatMod, got $other")
    }
  }

  test("parse natFloorDiv") {
    val n = parseNat(SExprParser.parseSExpr("(natFloorDiv 10n 3n)"))
    n match {
      case Nat(NatIntDiv(a, b)) =>
        assert(a == Nat(NatCst(10)))
        assert(b == Nat(NatCst(3)))
      case other => fail(s"Expected NatIntDiv, got $other")
    }
  }

  test("parse nested nat expression") {
    val n = parseNat(SExprParser.parseSExpr("(natAdd (natMul $n0 2n) 1n)"))
    n match {
      case Nat(NatAdd(Nat(NatMul(a, b)), c)) =>
        assert(a == Nat(NatVar(0)))
        assert(b == Nat(NatCst(2)))
        assert(c == Nat(NatCst(1)))
      case other => fail(s"Expected nested nat expression, got $other")
    }
  }

  // ==================== IndexLiteral parsing ====================

  test("parse index literal") {
    val expr = parse("(typeOf (idxL 3n 10n) (idxT 10n))")
    expr.node match {
      case IndexLiteral(i, n) =>
        assert(i == Nat(NatCst(3)))
        assert(n == Nat(NatCst(10)))
      case other => fail(s"Expected IndexLiteral, got $other")
    }
  }

  // ==================== Complex expression parsing ====================

  test("parse map applied to lambda") {
    val input =
      "(typeOf (app (typeOf map (fun (fun f32 f32) (fun (arrT 10n f32) (arrT 10n f32)))) (typeOf (lam (typeOf $e0 f32)) (fun f32 f32))) (fun (arrT 10n f32) (arrT 10n f32)))"
    val expr = parse(input)
    expr.node match {
      case App(f, e) =>
        f.node match {
          case Primitive(p) => assert(p.name == "map")
          case other        => fail(s"Expected map primitive, got $other")
        }
        e.node match {
          case Lambda(_) => // ok
          case other     => fail(s"Expected Lambda, got $other")
        }
      case other => fail(s"Expected App, got $other")
    }
  }

  test("parse the user's example expression") {
    val input =
      """(typeOf (natLam (typeOf (natLam (typeOf (natLam (typeOf (lam (typeOf (lam (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT $n0 f32) (arrT $n1 f32)) (fun (arrT $n2 (arrT $n0 f32)) (arrT $n2 (arrT $n1 f32))))) (typeOf (lam (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT $n0 f32) f32) (fun (arrT $n1 (arrT $n0 f32)) (arrT $n1 f32)))) (typeOf (lam (typeOf (app (typeOf (app (typeOf (app (typeOf reduce (fun (fun f32 (fun f32 f32)) (fun f32 (fun (arrT $n0 f32) f32)))) (typeOf add (fun f32 (fun f32 f32)))) (fun f32 (fun (arrT $n0 f32) f32))) (typeOf 0.0 f32)) (fun (arrT $n0 f32) f32)) (typeOf (app (typeOf (app (typeOf map (fun (fun (pairT f32 f32) f32) (fun (arrT $n0 (pairT f32 f32)) (arrT $n0 f32)))) (typeOf (lam (typeOf (app (typeOf (app (typeOf mul (fun f32 (fun f32 f32))) (typeOf (app (typeOf fst (fun (pairT f32 f32) f32)) (typeOf $e0 (pairT f32 f32))) f32)) (fun f32 f32)) (typeOf (app (typeOf snd (fun (pairT f32 f32) f32)) (typeOf $e0 (pairT f32 f32))) f32)) f32)) (fun (pairT f32 f32) f32))) (fun (arrT $n0 (pairT f32 f32)) (arrT $n0 f32))) (typeOf (app (typeOf (app (typeOf zip (fun (arrT $n0 f32) (fun (arrT $n0 f32) (arrT $n0 (pairT f32 f32))))) (typeOf $e1 (arrT $n0 f32))) (fun (arrT $n0 f32) (arrT $n0 (pairT f32 f32)))) (typeOf $e0 (arrT $n0 f32))) (arrT $n0 (pairT f32 f32)))) (arrT $n0 f32))) f32)) (fun (arrT $n0 f32) f32))) (fun (arrT $n1 (arrT $n0 f32)) (arrT $n1 f32))) (typeOf (app (typeOf transpose (fun (arrT $n0 (arrT $n1 f32)) (arrT $n1 (arrT $n0 f32)))) (typeOf $e1 (arrT $n0 (arrT $n1 f32)))) (arrT $n1 (arrT $n0 f32)))) (arrT $n1 f32))) (fun (arrT $n0 f32) (arrT $n1 f32)))) (fun (arrT $n2 (arrT $n0 f32)) (arrT $n2 (arrT $n1 f32)))) (typeOf $e1 (arrT $n2 (arrT $n0 f32)))) (arrT $n2 (arrT $n1 f32)))) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32))))) (fun (arrT $n2 (arrT $n0 f32)) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32)))))) (natFun (fun (arrT $n2 (arrT $n0 f32)) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32))))))) (natFun (natFun (fun (arrT $n2 (arrT $n0 f32)) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32)))))))) (natFun (natFun (natFun (fun (arrT $n2 (arrT $n0 f32)) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32))))))))"""

    val expr = parse(input)

    // Verify the structure: should be 3 nested natLam, then 2 lam, then the body
    expr.node match {
      case NatLambda(e1) =>
        e1.node match {
          case NatLambda(e2) =>
            e2.node match {
              case NatLambda(e3) =>
                e3.node match {
                  case Lambda(e4) =>
                    e4.node match {
                      case Lambda(e5) =>
                        // The innermost body should be an App
                        e5.node match {
                          case App(_, _) => // ok
                          case other     => fail(s"Expected App in innermost body, got $other")
                        }
                      case other => fail(s"Expected inner Lambda, got $other")
                    }
                  case other => fail(s"Expected outer Lambda, got $other")
                }
              case other => fail(s"Expected third NatLambda, got $other")
            }
          case other => fail(s"Expected second NatLambda, got $other")
        }
      case other => fail(s"Expected first NatLambda, got $other")
    }

    // Also verify the type structure
    expr.t match {
      case Type(NatFunType(Type(NatFunType(Type(NatFunType(_)))))) => // ok
      case other => fail(s"Expected nested NatFunType, got $other")
    }
  }

  // ==================== Error handling ====================

  test("parse error on unclosed parenthesis") {
    intercept[ParseException] {
      parse("(typeOf $e0 f32")
    }
  }

  test("parse error on unknown primitive") {
    intercept[ParseException] {
      parse("(typeOf unknownPrimitive f32)")
    }
  }

  test("parse error on malformed typeOf") {
    intercept[ParseException] {
      parse("(typeOf $e0)") // missing type
    }
  }

  test("parse error on bare atom") {
    intercept[ParseException] {
      parse("$e0") // not wrapped in typeOf
    }
  }

  // ==================== Round-trip tests ====================

  test("round-trip simple variable") {
    roundTrip("(typeOf $e0 f32)")
  }

  test("round-trip simple lambda") {
    roundTrip("(typeOf (lam (typeOf $e0 f32)) (fun f32 f32))")
  }

  test("round-trip application") {
    roundTrip("(typeOf (app (typeOf id (fun f32 f32)) (typeOf $e0 f32)) f32)")
  }

  test("round-trip natLam") {
    roundTrip("(typeOf (natLam (typeOf $e0 (arrT $n0 f32))) (natFun (arrT $n0 f32)))")
  }

  test("round-trip map with lambda") {
    roundTrip(
      "(typeOf (app (typeOf map (fun (fun f32 f32) (fun (arrT 10n f32) (arrT 10n f32)))) (typeOf (lam (typeOf $e0 f32)) (fun f32 f32))) (fun (arrT 10n f32) (arrT 10n f32)))"
    )
  }
}
