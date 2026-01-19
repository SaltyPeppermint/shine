package rise.eqsat

/*
 This package contains features to translate Rise expressions and rewrites
 to an egg-compatible language living in Rust.

 see https://github.com/Bastacyclop/reggvolution

 */
object Reggvolution {
  var anyCounter = 0
  def nextAny(): Int = {
    this.anyCounter += 1
    this.anyCounter - 1
  }

  // NOTE: could define reggvolution for generic nodes, but this is simpler
  def reggvolve(expr: Expr): String = reggvolve(Pattern.fromExpr(expr))

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

    val patVars: PatternVarMap[Expr.Shift, PatternVar] = HashMap()
    val natPatVars: PatternVarMap[Nat.Shift, NatPatternVar] = HashMap()
    val dataTypePatVars: PatternVarMap[Type.Shift, DataTypePatternVar] = HashMap()
    val typePatVars: PatternVarMap[Type.Shift, TypePatternVar] = HashMap()
    val addrPatVars: PatternVarMap[Address.Shift, AddressPatternVar] = HashMap()
    // nats which we need to pivot to avoid matching over certain nat constructs
    val natsToPivot = Vec[(rct.Nat, rct.NatIdentifier, Nat.Shift, NatPatternVar)]()

    val boundVarToShift = HashMap[String, Expr.Shift]()

    def shiftOfBound(bound: Expr.Bound): Expr.Shift =
      (bound.expr.size, bound.nat.size, bound.data.size, bound.addr.size, bound.n2n.size)

    def natShiftOfBound(bound: Expr.Bound): Nat.Shift = (bound.nat.size, bound.n2n.size)

    def typeShiftOfBound(bound: Expr.Bound): Type.Shift =
      (bound.nat.size, bound.data.size, bound.n2n.size)

    def addrShiftOfBound(bound: Expr.Bound): Address.Shift = bound.addr.size

    val lhsPat = makePat(
      typedLhs,
      Expr.Bound.empty,
      isRhs = false,
      freeV,
      freeT,
      shiftOfBound,
      natShiftOfBound,
      typeShiftOfBound,
      addrShiftOfBound,
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
      natShiftOfBound,
      typeShiftOfBound,
      addrShiftOfBound,
      patVars,
      natPatVars,
      dataTypePatVars,
      typePatVars,
      addrPatVars,
      natsToPivot,
      boundVarToShift
    )

    def patMkShift(s1: Expr.Shift, pv1: PatternVar)(s2: Expr.Shift, pv2: PatternVar)(
        applier: String
    ): String = {
      // println(s"printing pv1 from patMkShift: ${pv1}")
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2._1 - s1._1, s2._2 - s1._2, s2._3 - s1._3, s2._4 - s1._4, s2._5 - s1._5)
      s"""Shifted::new("${pv1}", "${pv2}", ${shift}.into(), ${cutoff}.into(), ${applier})"""
    }

    def patMkShiftCheck(s1: Expr.Shift, pv1: PatternVar)(s2: Expr.Shift, pv2: PatternVar)(
        applier: String
    ): String = {
      // println(s"printing pv1 from patMkShiftCheck: ${pv1}")
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2._1 - s1._1, s2._2 - s1._2, s2._3 - s1._3, s2._4 - s1._4, s2._5 - s1._5)
      s"""ShiftedCheck::new("${pv1}", "${pv2}", ${shift}.into(), ${cutoff}.into(), ${applier})"""
    }

    def natPatMkShift(s1: Nat.Shift, pv1: NatPatternVar)(s2: Nat.Shift, pv2: NatPatternVar)(
        applier: String
    ): String = {
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2._1 - s1._1, s2._2 - s1._2)
      s"""Shifted::new("${pv1}", "${pv2}", ${shift}.into(), ${cutoff}.into(), ${applier})"""
    }

    def natPatMkShiftCheck(s1: Nat.Shift, pv1: NatPatternVar)(s2: Nat.Shift, pv2: NatPatternVar)(
        applier: String
    ): String = {
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2._1 - s1._1, s2._2 - s1._2)
      s"""ShiftedCheck::new("${pv1}", "${pv2}", ${shift}.into(), ${cutoff}.into(), ${applier})"""
    }

    def dataTypePatMkShift(
        s1: Type.Shift,
        pv1: DataTypePatternVar
    )(s2: Type.Shift, pv2: DataTypePatternVar)(applier: String): String = {
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2._1 - s1._1, s2._2 - s1._2, s2._3 - s1._3)
      s"""Shifted::new("${pv1}", "${pv2}", ${shift}.into(), ${cutoff}.into(), ${applier})"""
    }

    def dataTypePatMkShiftCheck(
        s1: Type.Shift,
        pv1: DataTypePatternVar
    )(s2: Type.Shift, pv2: DataTypePatternVar)(applier: String): String = {
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2._1 - s1._1, s2._2 - s1._2, s2._3 - s1._3)
      s"""ShiftedCheck::new("${pv1}", "${pv2}", ${shift}.into(), ${cutoff}.into(), ${applier})"""
    }

    def typePatMkShift(s1: Type.Shift, pv1: TypePatternVar)(s2: Type.Shift, pv2: TypePatternVar)(
        applier: String
    ): String = {
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2._1 - s1._1, s2._2 - s1._2, s2._3 - s1._3)
      s"""Shifted::new("${pv1}", "${pv2}", ${shift}.into(), ${cutoff}.into(), ${applier})"""
    }

    def typePatMkShiftCheck(
        s1: Type.Shift,
        pv1: TypePatternVar
    )(s2: Type.Shift, pv2: TypePatternVar)(applier: String): String = {
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2._1 - s1._1, s2._2 - s1._2, s2._3 - s1._3)
      s"""ShiftedCheck::new("${pv1}", "${pv2}", ${shift}.into(), ${cutoff}.into(), ${applier})"""
    }

    def addrPatMkShift(
        s1: Address.Shift,
        pv1: AddressPatternVar
    )(s2: Address.Shift, pv2: AddressPatternVar)(applier: String): String = {
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2 - s1)
      // ShiftedAddressApplier(pv1, pv2, shift, cutoff, applier)
      ???
    }

    def addrPatMkShiftCheck(
        s1: Address.Shift,
        pv1: AddressPatternVar
    )(s2: Address.Shift, pv2: AddressPatternVar)(applier: String): String = {
      assert(s1 != s2)
      val cutoff = s1
      val shift = (s2 - s1)
      ???
    }

    def mkComputeNatCheck(pv: NatPatternVar, valuePat: NatPattern, applier: String): String = {
      val vp = reggvolve(valuePat)
      s"""ComputeNatCheck::new("${pv}", "${vp}", ${applier})"""
    }

    def mkComputeNat(pv: NatPatternVar, valuePat: NatPattern, applier: String): String = {
      val vp = reggvolve(valuePat)
      s"""ComputeNat::new("${pv}", "${vp}", ${applier})"""
    }

    val searcher: String = s"""RisePredicate::new(pat("${reggvolve(lhsPat)}"))"""
    val param = parameters.foldRight((a: String) => a) { case (c, acc) =>
      c match {
        case NotFreeIn(notFree, in) =>
          val nfShift = boundVarToShift.getOrElse(notFree, (0, 0, 0, 0, 0))._1
          // all left-hand-side uses of `in` may contain `notFree`
          assert(patVars(in).forall { case ((shift, _, _, _, _), (_, status)) =>
            shift >= nfShift || status != Known
          })
          // pick one of these uses
          val (iS, iPV) = patVars(in).collectFirst { case ((s, _, _, _, _), (pv, Known)) =>
            (s, pv)
          }.get
          val nfIndex = iS - nfShift // >= 0 because iS >= nfShift
          // NotFreeInApplier(iPV, nfIndex, acc(a))
          (a: String) => s"""NotFreeIn::new("${iPV}", ${nfIndex}, ${a})"""
        case VectorizeScalarFun(f, n, fV) =>
          val (nPV, nST) = natPatVars(n)(0, 0)
          assert(nST == Known)
          val (fPV, fST) = patVars(f)((0, 0, 0, 0, 0))
          assert(fST == Known)
          val fVPV = makePatVar(fV, (0, 0, 0, 0, 0), patVars, PatternVar, Known)
          // VectorizeScalarFunExtractApplier(fPV, nPV, fVPV, acc(a))
          (a: String) => s"""VectorizeScalarFun::new("${fPV}", "${nPV}", "${fVPV}", ${a})"""
      }
    }
    val rhsPatApplier = s"""DTCheck::new(pat("${reggvolve(rhsPat)}"))"""
    val shiftPV = shiftAppliers(patVars, patMkShift, patMkShiftCheck)
    val shiftNPV = shiftAppliers(natPatVars, natPatMkShift, natPatMkShiftCheck)
    val shiftDTPV = shiftAppliers(dataTypePatVars, dataTypePatMkShift, dataTypePatMkShiftCheck)
    val shiftTPV = shiftAppliers(typePatVars, typePatMkShift, typePatMkShiftCheck)
    val shiftAPV = shiftAppliers(addrPatVars, addrPatMkShift, addrPatMkShiftCheck)
    val pivotNPV = pivotNats(
      natsToPivot.toSeq,
      natPatVars,
      natPatMkShift,
      natPatMkShiftCheck,
      mkComputeNatCheck,
      mkComputeNat
    )
    val applier = param(shiftPV(shiftNPV(shiftDTPV(shiftTPV(shiftAPV(pivotNPV(rhsPatApplier)))))))

    def allIsShiftCoherent[S, V](pvm: PatternVarMap[S, V]): Boolean = pvm.forall {
      case (_, shiftMap) =>
        shiftMap.forall { case (_, (_, status)) => status == ShiftCoherent }
    }
    assert(allIsShiftCoherent(patVars))
    assert(allIsShiftCoherent(natPatVars))
    assert(allIsShiftCoherent(dataTypePatVars))
    assert(allIsShiftCoherent(typePatVars))
    assert(allIsShiftCoherent(addrPatVars))

    s"""rewrite!("${name}"; { ${searcher} } => { ${applier} }),"""
  }

  def reggvolve(pat: Pattern): String = {
    val e = pat.p match {
      case PatternVar(index) => s"?${index}"
      case PatternNode(node) =>
        node match {
          case Var(index)        => s"%e${index}"
          case App(f, e)         => s"(app ${reggvolve(f)} ${reggvolve(e)})"
          case NatApp(f, x)      => s"(natApp ${reggvolve(f)} ${reggvolve(x)})"
          case DataApp(f, x)     => s"(dataApp ${reggvolve(f)} ${reggvolve(x)})"
          case AddrApp(f, x)     => s"(addrApp ${reggvolve(f)} ${reggvolve(x)})"
          case AppNatToNat(f, x) => s"(natNatApp ${reggvolve(f)} ${reggvolve(x)})"
          case Lambda(e)         => s"(lam ${reggvolve(e)})"
          case NatLambda(e)      => s"(natLam ${reggvolve(e)})"
          case DataLambda(e)     => s"(dataLam ${reggvolve(e)})"
          case AddrLambda(e)     => s"(addrLam ${reggvolve(e)})"
          case LambdaNatToNat(e) => s"(natNatLam ${reggvolve(e)})"
          case Literal(d) =>
            import rise.core.semantics._

            d match {
              case BoolData(true)    => "true"
              case BoolData(false)   => "false"
              case IntData(value)    => s"${value}i" // s"Integer($value)"
              case FloatData(value)  => s"${value}" // s"Float($value)"
              case DoubleData(value) => s"${value}" // s"Double($value)"
              case _                 => throw new Exception(s"not supporting literal $d yet")
            }
          case NatLiteral(n)      => reggvolve(n)
          case IndexLiteral(i, n) => s"(idxL ${reggvolve(i)} ${reggvolve(n)})"
          case Primitive(p)       => p.name
          case Composition(f, g)  => ???
        }
    }
    val t = reggvolve(pat.t)
    s"(typeOf $e $t)"

  }

  def reggvolve(ty: TypePattern): String = {
    ty match {
      case TypePatternVar(index)     => s"?t${index}"
      case DataTypePatternVar(index) => s"?d${index}"
      case TypePatternAny            => s"?tAny${nextAny()}"
      case DataTypePatternAny        => s"?dAny${nextAny()}"
      case TypePatternNode(n) =>
        n match {
          case dt: DataTypeNode[_, _] =>
            reggvolve(rise.eqsat.DataTypePatternNode(dt))
          case FunType(a, b)      => s"(fun ${reggvolve(a)} ${reggvolve(b)})"
          case NatFunType(t)      => s"(natFun ${reggvolve(t)})"
          case DataFunType(t)     => s"(dataFun ${reggvolve(t)})"
          case AddrFunType(t)     => s"(addrFun ${reggvolve(t)})"
          case NatToNatFunType(t) => s"(natNatFun ${reggvolve(t)})"
          // TODO: do we need to remember the arg kind as a type ?
        }
      // FIXME: this construct is redundant ???
      case dtn: DataTypePatternNode => reggvolve(dtn)
    }
  }

  def reggvolve(n: NatPattern): String = {
    n match {
      case NatPatternVar(index) => s"?n${index}"
      case NatPatternAny        => s"?nAny${nextAny()}"
      case NatPatternNode(n) =>
        n match {
          case NatVar(index)     => s"%n${index}"
          case NatCst(value)     => s"${value}n"
          case NatNegInf         => ???
          case NatPosInf         => ???
          case NatAdd(a, b)      => s"(natAdd ${reggvolve(a)} ${reggvolve(b)})"
          case NatMul(a, b)      => s"(natMul ${reggvolve(a)} ${reggvolve(b)})"
          case NatPow(a, b)      => s"(natPow ${reggvolve(a)} ${reggvolve(b)})"
          case NatMod(a, b)      => s"(natMod ${reggvolve(a)} ${reggvolve(b)})"
          case NatIntDiv(a, b)   => s"(natFloorDiv ${reggvolve(a)} ${reggvolve(b)})"
          case NatToNatApp(f, n) => ???
        }
    }
  }

  def reggvolve(dty: DataTypePatternNode): String = {
    dty.n match {
      case DataTypeVar(index) => s"%d${index}"
      case ScalarType(s)      => s.toString()
      case NatType            => "natT"
      case IndexType(n)       => s"(idxT ${reggvolve(n)})"
      case PairType(dt1, dt2) => s"(pairT ${reggvolve(dt1)} ${reggvolve(dt2)})"
      case ArrayType(n, et)   => s"(arrT ${reggvolve(n)} ${reggvolve(et)})"
      case VectorType(n, et)  => s"(vecT ${reggvolve(n)} ${reggvolve(et)})"
    }
  }

  def reggvolve(a: AddressPattern): String = {
    a match {
      case AddressPatternVar(index) => s"?a${index}"
      case AddressPatternAny        => s"?aAny${nextAny()}"
      case AddressPatternNode(n) =>
        n match {
          case AddressVar(index) => s"%a${index}"
          case Global            => "global"
          case Local             => "local"
          case Private           => "private"
          case Constant          => "constant"
        }
    }
  }

  def reggvolve(n: NatToNatNode[NatPattern]): String = {
    ???
  }

}
