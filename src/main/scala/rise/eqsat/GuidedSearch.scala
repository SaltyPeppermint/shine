package rise.eqsat

import scala.language.existentials

object GuidedSearch {
  object Step {
    def init(nf: NF): Step =
      Step(nf, Seq(), SketchAny(TypePatternAny), BeamExtractor(1, AstSize))
  }

  case class Step(
      normalForm: NF,
      rules: Seq[Rewrite],
      sketch: Sketch,
      extractor: Extractor
  ) {
    def withNormalForm(nf: NF): Step =
      this.copy(normalForm = nf)

    def withRules(rs: Seq[Rewrite]): Step =
      this.copy(rules = rs)

    def withSketch(s: Sketch): Step =
      this.copy(sketch = s)

    def withExtractor(ex: Extractor): Step =
      this.copy(extractor = ex)

    def compose(other: Step): Step = {
      assert(normalForm == other.normalForm)
      val mergedRules = (rules ++ other.rules).distinctBy(_.name)
      Step(normalForm, mergedRules, other.sketch, other.extractor)
    }
  }

  trait Extractor {
    def extract(sketch: Sketch, egraph: EGraph, id: EClassId): Seq[Expr]
  }

  // TODO: accept normal form
  case class BeamExtractor(beamSize: Int, costFunction: CostFunction[_]) extends Extractor {
    override def extract(
        sketch: Sketch,
        egraph: EGraph,
        id: EClassId
    ): Seq[Expr] =
      Sketch
        .beamSearch(sketch, beamSize, costFunction, egraph, id)
        .map { case (_, e) => ExprWithHashCons.expr(egraph)(e) }
  }

  // no expr = failure
  case class Result(exprs: Seq[Expr], stats: Vec[Stats]) {
    def printReport(): Unit = {
      stats.zipWithIndex.foreach { case (st, i) =>
        println(s"  -- step n°$i")
        def ratio(a: Long, b: Long) = f"${a.toDouble / b.toDouble}%.2f"
        println(
          s"  iterations: ${st.iterations}, rewrites: ${st.rewriteCount}, nf rewrites: ${st.normRewriteCount}"
        )
        println(
          s"e-graph size: ${st.egraphNodes} nodes, ${st.egraphClasses} classes"
        )
        println(
          s"  total time: ${util.prettyTime(st.totalTime)} (" +
            s"${ratio(st.initializeTime, st.totalTime)} initialize, " +
            s"${ratio(st.rewriteSearchTime, st.totalTime)} rewrite search, " +
            s"${ratio(st.rewriteApplyTime, st.totalTime)} rewrite apply, " +
            s"${ratio(st.egraphRebuildTime, st.totalTime)} e-graph rebuild, " +
            s"${ratio(st.goalCheckTime, st.totalTime)} goal check, " +
            s"${ratio(st.extractionTime, st.totalTime)} extraction)"
        )
        println(s"  maximum memory ${st.memoryStats.pretty()}")
        // if (!stats.lift(i + 1).exists(_.beam.nonEmpty)) {
        st.beam.headOption.foreach { e =>
          println(s"  best expr:")
          println(Expr.toNamed(e))
          // util.dotPrintTmp(s"best_step${i}_", Expr.toNamed(e))
        }
      // }
      }
    }
  }

  case class Stats(
      initializeTime: Long,
      rewriteSearchTime: Long,
      rewriteApplyTime: Long,
      egraphRebuildTime: Long,
      goalCheckTime: Long,
      extractionTime: Long,
      totalTime: Long,
      iterations: Int,
      normRewriteCount: Long,
      rewriteCount: Long,
      egraphNodes: Int,
      egraphClasses: Int,
      memoryStats: util.MemoryStats,
      beam: Seq[Expr]
  )

  def init(): GuidedSearch = new GuidedSearch(
    filter = NoPredicate(),
    transformRunner = r => r
  )
}

class GuidedSearch(
    var filter: Predicate,
    var transformRunner: Runner => Runner
) {
  def withFilter(filter: Predicate): GuidedSearch = {
    this.filter = filter
    this
  }

  def withRunnerTransform(f: Runner => Runner): GuidedSearch = {
    transformRunner = f
    this
  }

  def run(
      start: rise.core.Expr,
      steps: Seq[GuidedSearch.Step]
  ): GuidedSearch.Result =
    run(Expr.fromNamed(start), steps)

  def run(
      start: rise.core.Expr,
      steps: Seq[GuidedSearch.Step],
      runName: String
  ): GuidedSearch.Result =
    run(Expr.fromNamed(start), steps, runName)

  def run(start: Expr, steps: Seq[GuidedSearch.Step]): GuidedSearch.Result =
    run(start, steps, "NONAME")

  def run(
      start: Expr,
      steps: Seq[GuidedSearch.Step],
      runName: String
  ): GuidedSearch.Result = run(
    start,
    steps,
    runName,
    0,
    false
  )

  def run(
      start: rise.core.Expr,
      steps: Seq[GuidedSearch.Step],
      runName: String,
      zs_hook: Boolean
  ): GuidedSearch.Result = run(
    Expr.fromNamed(start),
    steps,
    runName,
    0,
    zs_hook
  )

  def run(
      start: Expr,
      steps: Seq[GuidedSearch.Step],
      runName: String,
      recCount: Int,
      zs_hook: Boolean
  ): GuidedSearch.Result = {
    val stats = Vec.empty[GuidedSearch.Stats]

    val startTime = System.nanoTime()
    // note: this is a bit hacky
    val timeLimit = transformRunner(Runner.init()).timeLimit

    var beam: Seq[Expr] = Seq(start)
    var s = 0
    while (s < steps.length) {
      println(s"---- step n°$s")
      val step = steps(s)

      var normRewriteCount = 0L
      val (initializeTime, (egraph, rootId)) = util.time {
        val egraph = EGraph.empty()
        val normBeam = beam.map { e =>
          val (n, rc) = step.normalForm.normalizeCountRewrites(e)
          normRewriteCount += rc
          n
        }
        println(s"beam head: ${Expr.toNamed(normBeam.head)}")
        val rootId = normBeam
          .map(egraph.addExpr)
          .reduce[EClassId] { case (a, b) => egraph.union(a, b)._1 }
        egraph.rebuild(Seq(rootId))
        (egraph, rootId)
      }

      // TODO: add goal check to e-graph for incremental update?
      val mergedRules =
        (step.rules ++ step.normalForm.rules).distinctBy(_.name)
      val (growTime, runner) = util.time(
        transformRunner(Runner.init())
          // note: update time limit
          .withTimeLimit(
            java.time.Duration
              .ofNanos(timeLimit - (System.nanoTime() - startTime))
          )
          .doneWhen { _ =>
            util.printTime(
              "goal check",
              Sketch.exists(step.sketch, egraph, rootId)
            )

            Sketch.exists(step.sketch, egraph, rootId)
          }
          .run(egraph, filter, mergedRules, Seq(), Seq(rootId))
      )
      val found = runner.stopReasons.contains(Done)

      runner.iterations.zipWithIndex.foreach { case (iter, i) =>
        iter.serEGraph.toFile(
          s"json/ser_egraph_${runName}_step_${s}_iteration_${i}_root_${rootId.i}.json"
        )
      }
      val (extractionTime, newBeam) = if (found) {
        util.time(step.extractor.extract(step.sketch, egraph, rootId))
      } else {
        (0L, Seq())
      }

      val totalIterationsTime =
        runner.iterations.iterator.map(_.totalTime).sum
      stats += GuidedSearch.Stats(
        initializeTime = initializeTime,
        rewriteSearchTime = runner.iterations.iterator.map(_.searchTime).sum,
        rewriteApplyTime = runner.iterations.iterator.map(_.applyTime).sum,
        egraphRebuildTime = runner.iterations.iterator.map(_.rebuildTime).sum,
        goalCheckTime = growTime - totalIterationsTime,
        extractionTime = extractionTime,
        totalTime = initializeTime + growTime + extractionTime,
        iterations = runner.iterationCount(),
        normRewriteCount = normRewriteCount,
        rewriteCount = runner.iterations.map(_.applied.values.map(_.toLong).sum).sum,
        egraphNodes = runner.iterations.last.egraphNodes,
        egraphClasses = runner.iterations.last.egraphClasses,
        memoryStats = runner.iterations.iterator.map(_.memStats).reduce(_ max _),
        beam = newBeam
      )

      if (found) {
        assert(newBeam.nonEmpty)
      } else {
        runner.printReport()
        runner.iterations.foreach(println)
        if (recCount < 10 && zs_hook) {
          val (iter, i) = runner.iterations.zipWithIndex.last
          val egraphPath =
            s"json/ser_egraph_${runName}_step_${s}_iteration_${i}_root_${rootId.i}.json"
          iter.serEGraph.toFile(egraphPath)

          val staticFixMe =
            "(typeOf (natLam (typeOf (natLam (typeOf (natLam (typeOf (lam (typeOf (lam (typeOf (app (typeOf join (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT $n1 f32))) (arrT $n2 (arrT $n1 f32)))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32))) (arrT 32n (arrT $n1 f32))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32)))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT $n1 f32)))))) (typeOf (app (typeOf map (fun (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32)) (arrT $n1 f32)) (fun (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32))) (arrT 32n (arrT $n1 f32))))) (typeOf join (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32)) (arrT $n1 f32)))) (fun (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32))) (arrT 32n (arrT $n1 f32))))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32)))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT $n1 f32))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32))) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32)))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32)))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32))))))) (typeOf transpose (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32))) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32)))))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32)))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32)))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32)))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32))))))) (typeOf (app (typeOf map (fun (fun (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n f32))) (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32)))))) (typeOf (lam (typeOf (app (typeOf (app (typeOf (app (typeOf reduceSeq (fun (fun (arrT 32n (arrT 32n f32)) (fun (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (arrT 32n f32)))) (fun (arrT 32n (arrT 32n f32)) (fun (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n f32)))))) (typeOf (lam (typeOf (lam (typeOf (app (typeOf (lam (typeOf (app (typeOf (app (typeOf (app (typeOf reduceSeq (fun (fun (arrT 32n (arrT 32n f32)) (fun (arrT 32n (arrT 32n (pairT f32 f32))) (arrT 32n (arrT 32n f32)))) (fun (arrT 32n (arrT 32n f32)) (fun (arrT 4n (arrT 32n (arrT 32n (pairT f32 f32)))) (arrT 32n (arrT 32n f32)))))) (typeOf (lam (typeOf (lam (typeOf (app (typeOf (app (typeOf map (fun (fun (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32))) (arrT 32n f32)) (fun (arrT 32n (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32)))) (arrT 32n (arrT 32n f32))))) (typeOf (lam (typeOf (app (typeOf (app (typeOf map (fun (fun (pairT f32 (pairT f32 f32)) f32) (fun (arrT 32n (pairT f32 (pairT f32 f32))) (arrT 32n f32)))) (typeOf (lam (typeOf (app (typeOf (app (typeOf add (fun f32 (fun f32 f32))) (typeOf (app (typeOf fst (fun (pairT f32 (pairT f32 f32)) f32)) (typeOf $e0 (pairT f32 (pairT f32 f32)))) f32)) (fun f32 f32)) (typeOf (app (typeOf (app (typeOf mul (fun f32 (fun f32 f32))) (typeOf (app (typeOf fst (fun (pairT f32 f32) f32)) (typeOf (app (typeOf snd (fun (pairT f32 (pairT f32 f32)) (pairT f32 f32))) (typeOf $e0 (pairT f32 (pairT f32 f32)))) (pairT f32 f32))) f32)) (fun f32 f32)) (typeOf (app (typeOf snd (fun (pairT f32 f32) f32)) (typeOf (app (typeOf snd (fun (pairT f32 (pairT f32 f32)) (pairT f32 f32))) (typeOf $e0 (pairT f32 (pairT f32 f32)))) (pairT f32 f32))) f32)) f32)) f32)) (fun (pairT f32 (pairT f32 f32)) f32))) (fun (arrT 32n (pairT f32 (pairT f32 f32))) (arrT 32n f32))) (typeOf (app (typeOf (app (typeOf zip (fun (arrT 32n f32) (fun (arrT 32n (pairT f32 f32)) (arrT 32n (pairT f32 (pairT f32 f32)))))) (typeOf (app (typeOf fst (fun (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32))) (arrT 32n f32))) (typeOf $e0 (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32))))) (arrT 32n f32))) (fun (arrT 32n (pairT f32 f32)) (arrT 32n (pairT f32 (pairT f32 f32))))) (typeOf (app (typeOf snd (fun (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32))) (arrT 32n (pairT f32 f32)))) (typeOf $e0 (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32))))) (arrT 32n (pairT f32 f32)))) (arrT 32n (pairT f32 (pairT f32 f32))))) (arrT 32n f32))) (fun (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32))) (arrT 32n f32)))) (fun (arrT 32n (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32)))) (arrT 32n (arrT 32n f32)))) (typeOf (app (typeOf (app (typeOf zip (fun (arrT 32n (arrT 32n f32)) (fun (arrT 32n (arrT 32n (pairT f32 f32))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32))))))) (typeOf $e1 (arrT 32n (arrT 32n f32)))) (fun (arrT 32n (arrT 32n (pairT f32 f32))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32)))))) (typeOf $e0 (arrT 32n (arrT 32n (pairT f32 f32))))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (pairT f32 f32)))))) (arrT 32n (arrT 32n f32)))) (fun (arrT 32n (arrT 32n (pairT f32 f32))) (arrT 32n (arrT 32n f32))))) (fun (arrT 32n (arrT 32n f32)) (fun (arrT 32n (arrT 32n (pairT f32 f32))) (arrT 32n (arrT 32n f32)))))) (fun (arrT 32n (arrT 32n f32)) (fun (arrT 4n (arrT 32n (arrT 32n (pairT f32 f32)))) (arrT 32n (arrT 32n f32))))) (typeOf (app (typeOf fst (fun (pairT (arrT 32n (arrT 32n f32)) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n f32)))) (typeOf (app (typeOf unzip (fun (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))) (pairT (arrT 32n (arrT 32n f32)) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32)))) (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))) (fun (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))))))) (typeOf unzip (fun (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32)))) (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))))) (fun (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))))) (typeOf $e0 (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))))) (pairT (arrT 32n (arrT 32n f32)) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT 32n (arrT 32n f32)))) (fun (arrT 4n (arrT 32n (arrT 32n (pairT f32 f32)))) (arrT 32n (arrT 32n f32)))) (typeOf (app (typeOf transpose (fun (arrT 32n (arrT 4n (arrT 32n (pairT f32 f32)))) (arrT 4n (arrT 32n (arrT 32n (pairT f32 f32)))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT 32n (arrT 4n (pairT f32 f32))) (arrT 4n (arrT 32n (pairT f32 f32)))) (fun (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (arrT 4n (arrT 32n (pairT f32 f32))))))) (typeOf transpose (fun (arrT 32n (arrT 4n (pairT f32 f32))) (arrT 4n (arrT 32n (pairT f32 f32)))))) (fun (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (arrT 4n (arrT 32n (pairT f32 f32)))))) (typeOf (app (typeOf snd (fun (pairT (arrT 32n (arrT 32n f32)) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))))) (typeOf (app (typeOf unzip (fun (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))) (pairT (arrT 32n (arrT 32n f32)) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32)))) (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))) (fun (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))))))) (typeOf unzip (fun (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32)))) (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))))) (fun (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))))) (typeOf $e0 (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))))) (pairT (arrT 32n (arrT 32n f32)) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT 32n (arrT 4n (arrT 32n (pairT f32 f32)))))) (arrT 4n (arrT 32n (arrT 32n (pairT f32 f32)))))) (arrT 32n (arrT 32n f32)))) (fun (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n f32)))) (typeOf (app (typeOf (app (typeOf map (fun (fun (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))) (fun (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32)))))))) (typeOf (lam (typeOf (app (typeOf (app (typeOf zip (fun (arrT 32n f32) (fun (arrT 32n (arrT 4n (pairT f32 f32))) (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))))) (typeOf (app (typeOf fst (fun (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n f32))) (typeOf $e0 (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT 32n f32))) (fun (arrT 32n (arrT 4n (pairT f32 f32))) (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32)))))) (typeOf (app (typeOf snd (fun (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (arrT 4n (pairT f32 f32))))) (typeOf $e0 (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32)))))) (fun (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))))) (fun (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))))) (typeOf (app (typeOf (app (typeOf zip (fun (arrT 32n (arrT 32n f32)) (fun (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32)))))))) (typeOf $e1 (arrT 32n (arrT 32n f32)))) (fun (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))))) (typeOf $e0 (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT 32n (pairT (arrT 32n f32) (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT 32n (arrT 32n (pairT f32 (arrT 4n (pairT f32 f32))))))) (arrT 32n (arrT 32n f32)))) (fun (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (arrT 32n f32))))) (fun (arrT 32n (arrT 32n f32)) (fun (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32)))) (arrT 32n (arrT 32n f32)))))) (fun (arrT 32n (arrT 32n f32)) (fun (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n f32))))) (typeOf (app (typeOf generate (fun (fun (idxT 32n) (arrT 32n f32)) (arrT 32n (arrT 32n f32)))) (typeOf (lam (typeOf (app (typeOf generate (fun (fun (idxT 32n) f32) (arrT 32n f32))) (typeOf (lam (typeOf 0.0f f32)) (fun (idxT 32n) f32))) (arrT 32n f32))) (fun (idxT 32n) (arrT 32n f32)))) (arrT 32n (arrT 32n f32)))) (fun (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n f32)))) (typeOf (app (typeOf transpose (fun (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))))) (typeOf $e0 (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT 32n (arrT 32n f32)))) (fun (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))) (arrT 32n (arrT 32n f32))))) (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32)))))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32)))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))))))) (typeOf transpose (fun (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT 32n (arrT $n0 f32)) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT $n0 f32))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))))))) (typeOf (app (typeOf map (fun (fun (arrT $n0 f32) (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))) (fun (arrT 32n (arrT $n0 f32)) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))))) (typeOf (lam (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT 32n (arrT $n0 f32)) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))) (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT $n0 f32))) (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))))) (typeOf (lam (typeOf (app (typeOf transpose (fun (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 4n (pairT f32 f32)))) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT $n0 (pairT f32 f32)) (arrT (natMul (natPow 4n -1n) $n0) (arrT 4n (pairT f32 f32)))) (fun (arrT 32n (arrT $n0 (pairT f32 f32))) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 4n (pairT f32 f32))))))) (typeOf (natApp (typeOf split (natFun (fun (arrT (natMul $n1 (natMul (natPow 4n -1n) $n0)) (pairT f32 f32)) (arrT (natMul (natPow 4n -1n) $n1) (arrT $n0 (pairT f32 f32)))))) 4n) (fun (arrT $n0 (pairT f32 f32)) (arrT (natMul (natPow 4n -1n) $n0) (arrT 4n (pairT f32 f32)))))) (fun (arrT 32n (arrT $n0 (pairT f32 f32))) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 4n (pairT f32 f32)))))) (typeOf (app (typeOf (app (typeOf map (fun (fun (arrT $n0 f32) (arrT $n0 (pairT f32 f32))) (fun (arrT 32n (arrT $n0 f32)) (arrT 32n (arrT $n0 (pairT f32 f32)))))) (typeOf (app (typeOf zip (fun (arrT $n0 f32) (fun (arrT $n0 f32) (arrT $n0 (pairT f32 f32))))) (typeOf $e1 (arrT $n0 f32))) (fun (arrT $n0 f32) (arrT $n0 (pairT f32 f32))))) (fun (arrT 32n (arrT $n0 f32)) (arrT 32n (arrT $n0 (pairT f32 f32))))) (typeOf $e0 (arrT 32n (arrT $n0 f32)))) (arrT 32n (arrT $n0 (pairT f32 f32))))) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 4n (pairT f32 f32)))))) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))) (fun (arrT 32n (arrT $n0 f32)) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (fun (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT $n0 f32))) (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (typeOf (app (typeOf (natApp (typeOf split (natFun (fun (arrT (natMul $n2 (natMul (natPow 32n -1n) $n0)) (arrT $n1 f32)) (arrT (natMul (natPow 32n -1n) $n2) (arrT $n0 (arrT $n1 f32)))))) 32n) (fun (arrT $n1 (arrT $n0 f32)) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT $n0 f32))))) (typeOf (app (typeOf transpose (fun (arrT $n0 (arrT $n1 f32)) (arrT $n1 (arrT $n0 f32)))) (typeOf $e1 (arrT $n0 (arrT $n1 f32)))) (arrT $n1 (arrT $n0 f32)))) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT $n0 f32))))) (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))) (fun (arrT $n0 f32) (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32)))))))) (fun (arrT 32n (arrT $n0 f32)) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))))) (fun (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT $n0 f32))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))))) (typeOf (app (typeOf (natApp (typeOf split (natFun (fun (arrT (natMul $n3 (natMul (natPow 32n -1n) $n0)) (arrT $n1 f32)) (arrT (natMul (natPow 32n -1n) $n3) (arrT $n0 (arrT $n1 f32)))))) 32n) (fun (arrT $n2 (arrT $n0 f32)) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT $n0 f32))))) (typeOf $e1 (arrT $n2 (arrT $n0 f32)))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT $n0 f32))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT (natMul (natPow 4n -1n) $n0) (arrT 32n (arrT 4n (pairT f32 f32))))))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n (arrT 32n f32)))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT (natMul (natPow 32n -1n) $n1) (arrT 32n f32)))))) (arrT (natMul (natPow 32n -1n) $n2) (arrT 32n (arrT $n1 f32))))) (arrT $n2 (arrT $n1 f32)))) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32))))) (fun (arrT $n2 (arrT $n0 f32)) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32)))))) (natFun (fun (arrT $n2 (arrT $n0 f32)) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32))))))) (natFun (natFun (fun (arrT $n2 (arrT $n0 f32)) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32)))))))) (natFun (natFun (natFun (fun (arrT $n2 (arrT $n0 f32)) (fun (arrT $n0 (arrT $n1 f32)) (arrT $n2 (arrT $n1 f32))))))))"
          // Reggvolution.reggvolve(steps(0))
          println(s"Attempting zs hook via $egraphPath")
          import scala.sys.process._
          val shellResult =
            Seq(
              "./distance",
              egraphPath,
              "-e",
              staticFixMe,
              "-d",
              "structural",
              "count",
              "--histogram",
              "--scientific",
              "-l",
              "200",
              "-b",
              "1000000",
              "--distribution",
              "normal:2.5"
            ).!!
          println(shellResult)
          val expr = SExprParser.parse(shellResult.lines().toList().getLast())
          println(s"Continuing with: ${Expr.toNamed(expr)}")
          run(
            expr,
            steps,
            runName,
            recCount + 1,
            zs_hook
          )
        } else {
          println("Nothing found womp womp")
          return GuidedSearch.Result(Seq(), stats) // could not reach sketch
        }
      }

      beam = newBeam
      s += 1
    }

    // FIXME: avoid normalizing here, extract normalized terms instead?
    val finalBeam = beam.map(steps.last.normalForm.normalize)
    GuidedSearch.Result(finalBeam, stats)
  }
}
