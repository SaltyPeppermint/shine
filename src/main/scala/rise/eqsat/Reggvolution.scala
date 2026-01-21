package rise.eqsat

import scala.collection.mutable.LinkedHashMap
import scala.collection.immutable
import rise.core.types.DataType
import rise.core.{types => rct}

import scala.language.postfixOps
import scala.sys.process._
import java.io.{File, Writer, BufferedWriter, FileWriter}

import upickle.default._
import rise.core.semantics.NatData
import rise.core.semantics.IndexData
import rise.core.semantics.BoolData
import rise.core.semantics.IntData
import rise.core.semantics.FloatData
import rise.core.semantics.DoubleData
import rise.core.semantics.VectorData
import rise.core.semantics.ArrayData
import rise.core.semantics.PairData

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

object SerEGraph {
  implicit val ownerRw: ReadWriter[SerEGraph] = macroRW[SerEGraph]

  def from_egraph(egraph: EGraph): SerEGraph = {

    var classesToPrint = egraph.classes.values.toSeq

    // define all the nodes, clustered by eclass

    val classes = egraph.classes.toMap.map {
      case (id: EClassId, eclass: EClass) => {
        val children = eclass.nodes.map((node) => {
          val children = node.children().map((child) => egraph.find(child))
          val label = nodeLabel(node)
          SerENode(label, children.map((c) => SerId.p(egraph.find(c))).toSeq)
        })
        (id.i, SerEClass(SerId.p(eclass.t), children.toSeq))
      }
    }
    val unionFind = egraph.unionFind.parents.toSeq.map((id) => id.i)

    SerEGraph(
      classes = classes,
      unionFind = unionFind,
      natHashCon = egraph.hashConses.nats.nodes.toMap.map { case (id, node) =>
        (id.i, SerENode.parse(node))
      },
      dataTypeHashCon = egraph.hashConses.dataTypes.nodes.toMap.map { case (id, node) =>
        (id.i, SerENode.parse(node))
      },
      typeHashCon = egraph.hashConses.types.nodes.toMap.map { case (id, node) =>
        (id.i, SerENode.parse(node))

      }
    )

  }

  private def nodeLabel(n: ENode): String = {
    n match {
      case Var(index)        => s"%e$index"
      case App(_, _)         => "app"
      case Lambda(_)         => "lam"
      case NatApp(_, _)      => "natApp"
      case NatLambda(_)      => "natLam"
      case DataApp(_, _)     => "dataApp"
      case DataLambda(_)     => "dataLam"
      case AddrApp(_, a)     => "addrApp"
      case AddrLambda(_)     => "addrLam"
      case AppNatToNat(_, _) => "natNatApp"
      case LambdaNatToNat(_) => "natNatLam"
      case Literal(d) =>
        d match {
          // case NatData(n)      =>
          // case IndexData(i, n) =>
          // case BoolData(b)     =>
          // case IntData(i)      =>
          // case FloatData(f)    =>
          // case DoubleData(d)   =>
          // case VectorData(v)    =>
          // case ArrayData(a)     =>
          // case PairData(p1, p2) =>
          case NatData(n)      => s"${n}n"
          case BoolData(true)  => "true"
          case BoolData(false) => "false"
          case IntData(i)      => s"${i}i" // s"Integer($value)"
          case FloatData(f)    => s"${f}" // s"Float($value)"
          case DoubleData(d)   => s"${d}" // s"Double($value)"
          case _               => throw new Exception(s"not supporting literal $d yet")
        }
      case NatLiteral(n)      => "nat"
      case IndexLiteral(_, _) => "idx"
      case Primitive(p)       => p.toString()
      case Composition(_, _)  => ">>"
    }
  }
}

case class SerEGraph(
    classes: Map[Int, SerEClass],
    unionFind: Seq[Int],
    natHashCon: Map[Int, SerENode],
    dataTypeHashCon: Map[Int, SerENode],
    typeHashCon: Map[Int, SerENode]
) {
  def toFile(path: String): Unit = {
    val file = new File(path)
    val writer = new BufferedWriter(new FileWriter(file))
    try { writer.write(write(this)) }
    finally { writer.close() }
  }

  def print(path: String): Unit = {
    println(write(this))
  }
}

object SerEClass {
  implicit val ownerRw: ReadWriter[SerEClass] = macroRW[SerEClass]
}
case class SerEClass(ty: String, nodes: Seq[SerENode])

object SerENode {
  implicit val ownerRw: ReadWriter[SerENode] = macroRW[SerENode]

  def parse(node: NatNode[NatId]): SerENode = node match {
    case NatVar(index)     => SerENode(s"%n${index}", Seq.empty)
    case NatCst(value)     => SerENode(s"${value}n", Seq.empty)
    case NatNegInf         => ???
    case NatPosInf         => ???
    case NatAdd(a, b)      => SerENode("natAdd", Seq(SerId.p(a), SerId.p(b)))
    case NatMul(a, b)      => SerENode("natMul", Seq(SerId.p(a), SerId.p(b)))
    case NatPow(a, b)      => SerENode("natPow", Seq(SerId.p(a), SerId.p(b)))
    case NatMod(a, b)      => SerENode("natMod", Seq(SerId.p(a), SerId.p(b)))
    case NatIntDiv(a, b)   => SerENode("natFloorDiv", Seq(SerId.p(a), SerId.p(b)))
    case NatToNatApp(f, n) => ???
  }

  def parse(node: DataTypeNode[NatId, DataTypeId]): SerENode = node match {
    case DataTypeVar(index) => SerENode(s"%d${index}", Seq.empty)
    case ScalarType(s)      => SerENode(s.toString(), Seq.empty)
    case NatType            => SerENode("natT", Seq.empty)
    case IndexType(n)       => SerENode("idxT", Seq(SerId.p(n)))
    case PairType(dt1, dt2) =>
      SerENode("pairT", Seq(SerId.p(dt1), SerId.p(dt2)))
    case ArrayType(n, et)  => SerENode("arrT", Seq(SerId.p(n), SerId.p(et)))
    case VectorType(n, et) => SerENode("vecT", Seq(SerId.p(n), SerId.p(et)))
  }

  def parse(node: TypeNode[TypeId, NatId, DataTypeId]): SerENode = node match {
    case dt: DataTypeNode[_, _] => parse(dt)
    case FunType(a, b)          => SerENode("fun", Seq(SerId.p(a), SerId.p(b)))
    case NatFunType(t)          => SerENode("natFun", Seq(SerId.p(t)))
    case DataFunType(t)         => SerENode("dataFun", Seq(SerId.p(t)))
    case AddrFunType(t)         => SerENode("addrFun", Seq(SerId.p(t)))
    case NatToNatFunType(t)     => SerENode("natNatFun", Seq(SerId.p(t)))
  }

}

case class SerENode(node: String, children: Seq[String])

object SerId {
  def p(id: TypeId): String = id match {
    case DataTypeId(i)    => s"$id"
    case NotDataTypeId(i) => s"$id"
  }
  def p(id: DataTypeId): String = s"$id"
  def p(id: NatId): String = s"$id"
  def p(id: EClassId): String = s"$id"
}

object SerializedTerm {

  // def dump()

  def parse(pat: Expr): TypedSerTerm = pat.node match {
    case Var(index)        => TypedSerTerm(s"%e${index}", parse(pat.t), Seq.empty)
    case App(f, e)         => TypedSerTerm("app", parse(pat.t), Seq(parse(f), parse(e)))
    case NatApp(f, x)      => TypedSerTerm("natApp", parse(pat.t), Seq(parse(f), parse(x)))
    case DataApp(f, x)     => TypedSerTerm("dataApp", parse(pat.t), Seq(parse(f), parse(x)))
    case AddrApp(f, x)     => TypedSerTerm("addrApp", parse(pat.t), Seq(parse(f), parse(x)))
    case AppNatToNat(f, x) => ???
    case Lambda(e)         => TypedSerTerm("lam", parse(pat.t), Seq(parse(e)))
    case NatLambda(e)      => TypedSerTerm("natLam", parse(pat.t), Seq(parse(e)))
    case DataLambda(e)     => TypedSerTerm("dataLam", parse(pat.t), Seq(parse(e)))
    case AddrLambda(e)     => TypedSerTerm("addrLam", parse(pat.t), Seq(parse(e)))
    case LambdaNatToNat(e) => TypedSerTerm("natNatLam", parse(pat.t), Seq(parse(e)))
    case Literal(d) =>
      import rise.core.semantics._

      d match {
        case BoolData(true)  => TypedSerTerm("true", parse(pat.t), Seq.empty)
        case BoolData(false) => TypedSerTerm("false", parse(pat.t), Seq.empty)
        case IntData(value) =>
          TypedSerTerm(s"${value}i", parse(pat.t), Seq.empty) // s"Integer($value)"
        case FloatData(value) =>
          TypedSerTerm(s"${value}f", parse(pat.t), Seq.empty) // s"Float($value)"
        case DoubleData(value) =>
          TypedSerTerm(s"${value}d", parse(pat.t), Seq.empty) // s"Double($value)"
        case _ => throw new Exception(s"not supporting literal $d yet")
      }
    case NatLiteral(n)      => TypedSerTerm(n.toString(), parse(pat.t), Seq.empty)
    case IndexLiteral(i, n) => TypedSerTerm("idxL", parse(pat.t), Seq(parse(i), parse(n)))
    case Primitive(p)       => TypedSerTerm(p.name, parse(pat.t), Seq.empty)
    case Composition(f, g)  => ???

  }

  def parse(ty: Type): UnTypedSerTerm = ty.node match {
    case dt: DataTypeNode[_, _] =>
      parse(rise.eqsat.DataType(dt))
    case FunType(a, b)      => UnTypedSerTerm("fun", Seq(parse(a), parse(b)))
    case NatFunType(t)      => UnTypedSerTerm("natFun", Seq(parse(t)))
    case DataFunType(t)     => UnTypedSerTerm("dataFun", Seq(parse(t)))
    case AddrFunType(t)     => UnTypedSerTerm("addrFun", Seq(parse(t)))
    case NatToNatFunType(t) => UnTypedSerTerm("natNatFun", Seq(parse(t)))

  }

  def parse(n: Nat): UnTypedSerTerm = n.node match {
    // case NatPatternVar(index) => parse(s"?n${index}")
    // case NatPatternAny        => parse(s"?nAny")
    // case NatPatternNode(n) =>
    //   n match {
    case NatVar(index)     => UnTypedSerTerm(s"%n${index}", Seq.empty)
    case NatCst(value)     => UnTypedSerTerm(s"${value}n", Seq.empty)
    case NatNegInf         => ???
    case NatPosInf         => ???
    case NatAdd(a, b)      => UnTypedSerTerm("natAdd", Seq(parse(a), parse(b)))
    case NatMul(a, b)      => UnTypedSerTerm("natMul", Seq(parse(a), parse(b)))
    case NatPow(a, b)      => UnTypedSerTerm("natPow", Seq(parse(a), parse(b)))
    case NatMod(a, b)      => UnTypedSerTerm("natMod", Seq(parse(a), parse(b)))
    case NatIntDiv(a, b)   => UnTypedSerTerm("natFloorDiv", Seq(parse(a), parse(b)))
    case NatToNatApp(f, n) => ???
    // }
  }

  def parse(dty: rise.eqsat.DataType): UnTypedSerTerm = dty.node match {
    case DataTypeVar(index) => UnTypedSerTerm(s"%d${index}", Seq.empty)
    case ScalarType(s)      => UnTypedSerTerm(s.toString(), Seq.empty)
    case NatType            => UnTypedSerTerm("natT", Seq.empty)
    case IndexType(n)       => UnTypedSerTerm("idxT", Seq(parse(n)))
    case PairType(dt1, dt2) =>
      UnTypedSerTerm("pairT", Seq(parse(dt1), parse(dt2)))
    case ArrayType(n, et)  => UnTypedSerTerm("arrT", Seq(parse(n), parse(et)))
    case VectorType(n, et) => UnTypedSerTerm("vecT", Seq(parse(n), parse(et)))
  }

  def parse(a: Address): UnTypedSerTerm = a match {
    case AddressVar(index) => UnTypedSerTerm(s"%a${index}", Seq.empty)
    case Global            => UnTypedSerTerm("global", Seq.empty)
    case Local             => UnTypedSerTerm("local", Seq.empty)
    case Private           => UnTypedSerTerm("private", Seq.empty)
    case Constant          => UnTypedSerTerm("constant", Seq.empty)

  }
}

sealed trait SerializedTerm

case class TypedSerTerm(
    node: String,
    ty: UnTypedSerTerm,
    children: Seq[SerializedTerm]
) extends SerializedTerm

case class UnTypedSerTerm(
    node: String,
    children: Seq[UnTypedSerTerm]
) extends SerializedTerm {}
