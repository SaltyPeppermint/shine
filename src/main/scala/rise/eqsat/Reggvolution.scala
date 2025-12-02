package rise.eqsat

/*
 This package contains features to translate Rise expressions and rewrites
 to an egg-compatible language living in Rust.

 see https://github.com/Bastacyclop/reggvolution

 */
object Reggvolution {
  // def sym(s: String): String = s
  // s"""sym("$s")"""

  // cascade of apps bearing no types, used to encode many language constructs
  // as simple symbol applications
  // def noTyApp(f: String, args: Iterable[String]): String = {
  //   args.foldLeft(f) { case (acc, arg) =>
  //     s"(app $acc $arg)"
  //   // s"App([$acc, $arg])"
  //   }
  // }

  var anyCounter = 0
  def nextAny(): Int = {
    this.anyCounter += 1
    this.anyCounter - 1
  }

  type Shift = rise.eqsat.Expr.Shift

  def reggvolve(expr: Expr): String =
    // NOTE: could define reggvolution for generic nodes, but this is simpler
    reggvolve(Pattern.fromExpr(expr))

  // same as NamedRewrite.init, but flattens DeBruijn indices from different kinds.
  // TODO: could factorize even more
  def reggvolveNamedRewrite(
      name: String,
      rule: (NamedRewriteDSL.Pattern, NamedRewriteDSL.Pattern),
      parameters: Seq[NamedRewrite.Parameter] = Seq()
  ): String = {
    import rise.core.DSL.infer
    import arithexpr.{arithmetic => ae}
    import rise.eqsat.NamedRewrite._
    import rise.core.types.DataKind.IDWrapper
    import rise.{core => rc}
    import rise.core.{types => rct}
    import rise.core.types.{DataType => rcdt}

    val (typedLhs, freeV, freeT, typedRhs) = typeRule(rule, parameters)

    type FlatShift = Int
    val patVars: PatternVarMap[FlatShift, PatternVar] = HashMap()
    val natPatVars: PatternVarMap[FlatShift, NatPatternVar] = HashMap()
    val dataTypePatVars: PatternVarMap[FlatShift, DataTypePatternVar] =
      HashMap()
    val typePatVars: PatternVarMap[FlatShift, TypePatternVar] = HashMap()
    val addrPatVars: PatternVarMap[FlatShift, AddressPatternVar] = HashMap()

    // nats which we need to pivot to avoid matching over certain nat constructs
    val natsToPivot =
      Vec[(rct.Nat, rct.NatIdentifier, FlatShift, NatPatternVar)]()

    val boundVarToShift = HashMap[String, FlatShift]()

    def shiftOfBound(bound: Expr.Bound): FlatShift =
      bound.expr.size + bound.nat.size + bound.data.size + bound.addr.size + bound.n2n.size

    val lhsPat = makePat(
      typedLhs,
      Expr.Bound.empty,
      isRhs = false,
      freeV,
      freeT,
      shiftOfBound,
      shiftOfBound,
      shiftOfBound,
      shiftOfBound,
      patVars,
      natPatVars,
      dataTypePatVars,
      typePatVars,
      addrPatVars,
      natsToPivot,
      boundVarToShift
    )
    val rhsPat = makePat(
      typedRhs,
      Expr.Bound.empty,
      isRhs = true,
      freeV,
      freeT,
      shiftOfBound,
      shiftOfBound,
      shiftOfBound,
      shiftOfBound,
      patVars,
      natPatVars,
      dataTypePatVars,
      typePatVars,
      addrPatVars,
      natsToPivot,
      boundVarToShift
    )

    def patMkShift(s1: FlatShift, pv1: Any)(s2: FlatShift, pv2: Any)(
        applier: String
    ): String = {
      // println(s"printing pv1 from patMkShift: ${pv1}")
      assert(s1 != s2)
      val cutoff = s1
      val shift = s2 - s1
      s"""Shifted::new("${pv1}", "${pv2}", ${shift}, ${cutoff}, ${applier})"""
    }

    def patMkShiftCheck(s1: FlatShift, pv1: Any)(s2: FlatShift, pv2: Any)(
        applier: String
    ): String = {
      // println(s"printing pv1 from patMkShiftCheck: ${pv1}")
      assert(s1 != s2)
      val cutoff = s1
      val shift = s2 - s1
      s"""ShiftedCheck::new("${pv1}", "${pv2}", ${shift}, ${cutoff}, ${applier})"""
    }

    def mkComputeNatCheck(
        pv: NatPatternVar,
        valuePat: NatPattern,
        applier: String
    ): String = {
      val vp = reggvolve(valuePat)
      s"""ComputeNatCheck::new("${pv}", "${vp}", ${applier})"""
    }

    def mkComputeNat(
        pv: NatPatternVar,
        valuePat: NatPattern,
        applier: String
    ): String = {
      val vp = reggvolve(valuePat)
      s"""ComputeNat::new("${pv}", "${vp}", ${applier})"""
    }

    val searcher: String = s""""${reggvolve(lhsPat)}""""
    val param = parameters.foldRight((a: String) => a) { case (c, acc) =>
      c match {
        case NotFreeIn(notFree, in) =>
          val nfShift = boundVarToShift.getOrElse(notFree, 0)
          // all left-hand-side uses of `in` may contain `notFree`
          assert(patVars(in).forall { case (shift, (_, status)) =>
            shift >= nfShift || status != Known
          })
          // pick one of these uses
          val (iS, iPV) = patVars(in).collectFirst { case (s, (pv, Known)) =>
            (s, pv)
          }.get
          val nfIndex = iS - nfShift // >= 0 because iS >= nfShift
          (a: String) =>
            s"""NotFreeIn::new("${iPV}", ${nfIndex}, ${a})"""
          // NotFreeInApplier(iPV, nfIndex, acc(a))
        case VectorizeScalarFun(f, n, fV) =>
          val (nPV, nST) = natPatVars(n)(0)
          assert(nST == Known)
          val (fPV, fST) = patVars(f)(0)
          assert(fST == Known)
          val fVPV = makePatVar(fV, 0, patVars, PatternVar, Known)
          (a: String) =>
            s"""VectorizeScalarFun::new("${fPV}", "${nPV}", "${fVPV}", ${a})"""
        // VectorizeScalarFunExtractApplier(fPV, nPV, fVPV, acc(a))
      }
    }
    val rhsPatApplier = s"""pat("${reggvolve(rhsPat)}")"""
    val shiftPV = shiftAppliers(patVars, patMkShift, patMkShiftCheck)
    val shiftNPV = shiftAppliers(natPatVars, patMkShift, patMkShiftCheck)
    val shiftDTPV = shiftAppliers(dataTypePatVars, patMkShift, patMkShiftCheck)
    val shiftTPV = shiftAppliers(typePatVars, patMkShift, patMkShiftCheck)
    val shiftAPV = shiftAppliers(addrPatVars, patMkShift, patMkShiftCheck)
    val pivotNPV = pivotNats(
      natsToPivot.toSeq,
      natPatVars,
      patMkShift,
      patMkShiftCheck,
      mkComputeNatCheck,
      mkComputeNat
    )
    val applier = param(
      shiftPV(shiftNPV(shiftDTPV(shiftTPV(shiftAPV(pivotNPV(rhsPatApplier))))))
    )

    def allIsShiftCoherent[S, V](pvm: PatternVarMap[S, V]): Boolean =
      pvm.forall { case (_, shiftMap) =>
        shiftMap.forall { case (_, (_, status)) => status == ShiftCoherent }
      }
    assert(allIsShiftCoherent(patVars))
    assert(allIsShiftCoherent(natPatVars))
    assert(allIsShiftCoherent(dataTypePatVars))
    assert(allIsShiftCoherent(typePatVars))
    assert(allIsShiftCoherent(addrPatVars))

    s"""rewrite!("${name}"; ${searcher} => { ${applier} }),"""
  }

  // DEPRECATED:
  // def reggvolve(searcher: Searcher): String =
  // def reggvolve(applier: Applier): String =

  // type FShift = (Int => Int, Int => Int, Int => Int, Int => Int, Int => Int);

  def reggvolve(pat: Pattern): String =
    reggvolve(pat, new FShift)

  def reggvolve(pat: NatPattern): String =
    reggvolve(pat, new FShift)

  def reggvolve(pat: Pattern, s: FShift): String = {
    val e = pat.p match {
      case PatternVar(index) => s"?${index}"
      case PatternNode(node) =>
        node match {
          case Var(index) => s"%e${s.expr(index)}"
          // s"Var(${index + s._1})"
          case App(f, e) => s"(app ${reggvolve(f, s)} ${reggvolve(e, s)})"
          // s"App([${reggvolve(f, s)}, ${reggvolve(e, s)}])"
          case NatApp(f, x) => s"(natApp ${reggvolve(f, s)} ${reggvolve(x, s)})"
          case DataApp(f, x) =>
            s"(dataApp ${reggvolve(f, s)} ${reggvolve(x, s)})"
          case AddrApp(f, x) =>
            s"(addrApp ${reggvolve(f, s)} ${reggvolve(x, s)})"
          case AppNatToNat(f, x) =>
            s"(natNatApp ${reggvolve(f, s)} ${reggvolve(x, s)})"
          case Lambda(e) =>
            val s2 = s.exprShift();
            s"(lam ${reggvolve(e, s2)})"
          case NatLambda(e) =>
            val s2 = s.natShift();
            s"(natLam ${reggvolve(e, s2)})"
          case DataLambda(e) =>
            val s2 = s.dataShift();
            s"(dataLam ${reggvolve(e, s2)})"
          case AddrLambda(e) =>
            val s2 = s.addrShift();
            s"(addrLam ${reggvolve(e, s2)})"
          case LambdaNatToNat(e) =>
            val s2 = s.natNatShift();
            s"(natNatLam ${reggvolve(e, s2)})"
          case Literal(d) =>
            import rise.core.semantics._

            d match {
              case BoolData(true)  => "true"
              case BoolData(false) => "false"
              case IntData(i)      => i.toString() // s"Integer($i)"
              case FloatData(f)    => f.toString() // s"Float($f)"
              case DoubleData(d)   => d.toString() // s"Double($d)"
              case _ => throw new Exception(s"not supporting literal $d yet")
            }
          case NatLiteral(n) => reggvolve(n, s)
          case IndexLiteral(i, n) =>
            s"(idxL ${reggvolve(i, s)} ${reggvolve(n, s)})"
          // case IndexLiteral(i, n) =>
          //   noTyApp(sym("idxL"), List(i, n).map(reggvolve(_, s)))
          case Primitive(p)      => p.name
          case Composition(f, g) => ???
        }
    }
    val t = reggvolve(pat.t, s)
    // s"TypeOf([$e, $t])"
    s"(typeOf $e $t)"

  }

  def reggvolve(ty: TypePattern, s: FShift): String = {
    ty match {
      case TypePatternVar(index)     => s"?t${index}"
      case DataTypePatternVar(index) => s"?dt${index}"
      case TypePatternAny            => s"?tAny${nextAny()}"
      case DataTypePatternAny        => s"?dtAny${nextAny()}"
      case TypePatternNode(n) =>
        n match {
          case dt: DataTypeNode[_, _] =>
            reggvolve(rise.eqsat.DataTypePatternNode(dt), s)
          case FunType(a, b) =>
            s"(fun ${reggvolve(a, s)} ${reggvolve(b, s)})"
          // noTyApp(sym("fun"), List(a, b).map(reggvolve(_, s)))
          // TODO: do we need to remember the arg kind as a type ?
          case NatFunType(t) =>
            val s2 = s.natShift()
            s"(natFun ${reggvolve(t, s2)})"
          case DataFunType(t) =>
            val s2 = s.dataShift();
            s"(dataFun ${reggvolve(t, s2)})"
          case AddrFunType(t) =>
            val s2 = s.addrShift();
            s"(addrFun ${reggvolve(t, s2)})"
          case NatToNatFunType(t) =>
            val s2 = s.natNatShift();
            s"(natNatFun ${reggvolve(t, s2)})"
        }
      // FIXME: this construct is redundant ???
      case dtn: DataTypePatternNode => reggvolve(dtn, s)
    }
  }

  def reggvolve(n: NatPattern, s: FShift): String = {
    n match {
      case NatPatternVar(index) => s"?n${index}"
      case NatPatternAny        => s"?nAny${nextAny()}"
      case NatPatternNode(n) =>
        n match {
          case NatVar(index) => s"%n${s.nat(index)}"
          case NatCst(value) => value.toString()
          case NatNegInf     => ???
          case NatPosInf     => ???
          case NatAdd(a, b) => s"(natAdd ${reggvolve(a, s)} ${reggvolve(b, s)})"
          //  noTyApp(sym("add"), List(a, b).map(reggvolve(_, s)))
          case NatMul(a, b) => s"(natMul ${reggvolve(a, s)} ${reggvolve(b, s)})"
          //  noTyApp(sym("mul"), List(a, b).map(reggvolve(_, s)))
          case NatPow(a, b) => s"(natPow ${reggvolve(a, s)} ${reggvolve(b, s)})"
          //  noTyApp(sym("pow"), List(a, b).map(reggvolve(_, s)))
          case NatMod(a, b) => s"(natMod ${reggvolve(a, s)} ${reggvolve(b, s)})"
          //  noTyApp(sym("mod"), List(a, b).map(reggvolve(_, s)))
          case NatIntDiv(a, b) =>
            s"(natFloorDiv ${reggvolve(a, s)} ${reggvolve(b, s)})"
          //  noTyApp(sym("floorDiv"), List(a, b).map(reggvolve(_, s)))
          case NatToNatApp(f, n) => ???
        }
    }
  }

  def reggvolve(dty: DataTypePatternNode, s: FShift): String = {
    dty.n match {
      case DataTypeVar(index) => s"%d${s.data(index)}"
      case ScalarType(s)      => s.toString()
      case NatType            => "natT"
      case IndexType(n)       => s"(idxT ${reggvolve(n, s)})"
      // noTyApp(sym("idxT"), List(reggvolve(n, s)))
      case PairType(dt1, dt2) =>
        s"(pairT ${reggvolve(dt1, s)} ${reggvolve(dt2, s)})"
      //  noTyApp(sym("pairT"), List(dt1, dt2).map(reggvolve(_, s)))
      case ArrayType(n, et) => s"(arrT ${reggvolve(n, s)} ${reggvolve(et, s)})"
      // noTyApp(sym("arrT"), List(reggvolve(n, s), reggvolve(et, s)))
      case VectorType(n, et) => s"(vecT ${reggvolve(n, s)} ${reggvolve(et, s)})"
      //  noTyApp(sym("vecT"), List(reggvolve(n, s), reggvolve(et, s)))
    }
  }

  def reggvolve(a: AddressPattern, s: FShift): String = {
    a match {
      case AddressPatternVar(index) => s"?a${index}"
      case AddressPatternAny        => s"?aAny${nextAny()}"
      case AddressPatternNode(n) =>
        n match {
          case AddressVar(index) => s"%a${s.addr(index)}"
          case Global            => "global"
          case Local             => "local"
          case Private           => "private"
          case Constant          => "constant"
        }
    }
  }

  def reggvolve(n: NatToNatNode[NatPattern], s: FShift): String = {
    ???
  }

}

class FShift(
    var expr: Int => Int,
    var nat: Int => Int,
    var data: Int => Int,
    var addr: Int => Int,
    var natNat: Int => Int
) {
  private def cond(s: Int => Int): Int => Int = { i =>
    {
      var x = s(i)
      if (i < x) x + 1 else i
    }

  }

  def this() = {
    this(
      Function.const(0: Int),
      Function.const(0: Int),
      Function.const(0: Int),
      Function.const(0: Int),
      Function.const(0: Int)
    )
  }

  def exprShift(): FShift = {

    new FShift(
      cond(this.expr),
      this.nat,
      this.data,
      this.addr,
      this.natNat
    )
  }

  def natShift(): FShift = {
    new FShift(
      this.expr,
      cond(this.nat),
      this.data,
      this.addr,
      this.natNat
    )
  }
  def dataShift(): FShift = {
    new FShift(
      this.expr,
      this.nat,
      cond(this.data),
      this.addr,
      this.natNat
    )
  }
  def addrShift(): FShift = {
    new FShift(
      this.expr,
      this.nat,
      this.data,
      cond(this.addr),
      this.natNat
    )
  }
  def natNatShift(): FShift = {
    new FShift(
      this.expr,
      this.nat,
      this.data,
      this.addr,
      cond(this.natNat)
    )
  }
}
