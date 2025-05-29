package org.renaissance.scala.sat

import java.util.concurrent.Executors
import java.util.concurrent.ExecutorService
import java.util.concurrent.ThreadPoolExecutor
import java.util.concurrent.TimeUnit
import cafesat.api.FormulaBuilder.and
import cafesat.api.FormulaBuilder.or
import cafesat.api.FormulaBuilder.propVar
import cafesat.api.Solver.solveForSatisfiability
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

object Solver {

  /**
   * Solver takes a sudoku problem as a matrix of optional integers
   * and fills in the missing values to form a correct Sudoku grid.
   */
  def solve(sudoku: Array[Array[Option[Int]]], sqrt_dim: Int): Option[Array[Array[Int]]] = {

    val dim = sqrt_dim*sqrt_dim

    /**
     * Each slot on the Sudoku board has `dim` associated variables (V0..V[dim-1]),
     * each variable Vi denoting whether the digit Vi was chosen for the
     * respective slot.
     */
    require(sudoku.length == dim)
    require(sudoku.forall(row => row.length == dim))

    val vars = sudoku.map(row => row.map(_ => Array.fill(dim)(propVar())))

    /**
     * There should be at least one digit chosen for each sudoku slot.
     */
    val onePerEntry = vars.flatMap(row => row.map(vs => or(vs.toIndexedSeq: _*)))

    /**
     * There must be at most one any digit in each sqrt_dim*sqrt_dim table.
     * Here, `k` is the variable (digit), `i` and `j` are the coordinates of the sqrt_dim*sqrt_dim tables,
     * `r1` and `r2` are row pairs within the sqrt_dim*sqrt_dim table, and `c1` and `c2` are pairs of
     * columns within the sqrt_dim*sqrt_dim table.
     */
    val uniqueInGrid1 =
      for (
        k <- 0 until dim; i <- 0 until sqrt_dim; j <- 0 until sqrt_dim; r <- 0 until sqrt_dim;
        c1 <- 0 to 1; c2 <- c1 + 1 until sqrt_dim
      )
        yield !vars(sqrt_dim * i + r)(sqrt_dim * j + c1)(k) || !vars(sqrt_dim * i + r)(sqrt_dim * j + c2)(k)

    val uniqueInGrid2 =
      for (
        k <- 0 until dim; i <- 0 until sqrt_dim; j <- 0 until sqrt_dim; r1 <- 0 until sqrt_dim;
        c1 <- 0 until sqrt_dim; c2 <- 0 until sqrt_dim; r2 <- r1 + 1 until sqrt_dim
      )
        yield !vars(sqrt_dim * i + r1)(sqrt_dim * j + c1)(k) || !vars(sqrt_dim * i + r2)(sqrt_dim * j + c2)(k)

    /**
     * In the respective column, there should be at most one unique digit.
     */
    val uniqueInColumns =
      for (c <- 0 until dim; k <- 0 until dim; r1 <- 0 until (dim-1); r2 <- (r1+1) until dim)
        yield !vars(r1)(c)(k) || !vars(r2)(c)(k)

    /**
     * In the respective row, there should be at most one unique digit.
     */
    val uniqueInRows =
      for (r <- 0 until dim; k <- 0 until dim; c1 <- 0 until (dim-1); c2 <- (c1+1) until dim)
        yield !vars(r)(c1)(k) || !vars(r)(c2)(k)

    /**
     * Force entry with a possible number.
     */
    val forcedEntries =
      for (r <- 0 until dim; c <- 0 until dim if sudoku(r)(c).isDefined)
        yield or(vars(r)(c)(sudoku(r)(c).get - 1))

    /**
     * All constraints for a sudoku problem.
     */
    val allConstraints = onePerEntry ++ uniqueInColumns ++ uniqueInRows ++
      uniqueInGrid1 ++ uniqueInGrid2 ++ forcedEntries

    /**
     * The whole grid should Satisfy all constraints.
     */
    solveForSatisfiability(and(allConstraints.toIndexedSeq: _*))
      .map(model => vars.map(row => row.map(vs => vs.indexWhere(v => model(v)) + 1)))
  }

}

@Name("scala-doku")
@Group("scala")
@Group("scala-sat")
@Summary("Solves Sudoku Puzzles using Scala collections.")
@Licenses(Array(License.MIT))
@Repetitions(20)
@Parameter(name = "sqrt_dim", defaultValue = "3")
@Parameter(name = "copies", defaultValue = "1")
@Parameter(name = "threads", defaultValue = "1")
@Parameter(name = "kill_after_seconds", defaultValue = "300")
@Configuration(name = "test")
@Configuration(name = "jmh")
final class ScalaDoku extends Benchmark {

  private var solved_puzzle: Array[Array[Int]] = _
  private var puzzles: Array[ Array[Array[Option[Int]]] ] = _

  private def prepareSolvedPuzzle(sqrt_dim: Int) = {
    /* Example for n=3:

    1 2 3   4 5 6   7 8 9
    4 5 6   7 8 9   1 2 3
    7 8 9   1 2 3   4 5 6

    2 3 4   5 6 7   8 9 1
    5 6 7   8 9 1   2 3 4
    8 9 1   2 3 4   5 6 7

    3 4 5   6 7 8   9 1 2
    6 7 8   9 1 2   3 4 5
    9 1 2   3 4 5   6 7 8
    */
    val dim = sqrt_dim*sqrt_dim
    val puzzle = new Array[Array[Int]](dim)

    for (big_i <- 0 until sqrt_dim) {
      for (small_i <- 0 until sqrt_dim) {
        val i = sqrt_dim*big_i + small_i
        puzzle(i) = new Array[Int](dim)
        for (j <- 0 until dim) {
          puzzle(i)(j) = ((big_i + sqrt_dim*small_i + j) % dim) + 1
        }
      }
    }

    puzzle
  }

  private def preparePuzzleWithAFewHoles(solved_puzzle: Array[Array[Int]]) = {
    val result = solved_puzzle.map(row => row.map(i => Some(i): Option[Int]))
    val permutation = new scala.util.Random(42).shuffle(Range(0, solved_puzzle.length))

    for (j <- 0 until solved_puzzle.length) {
      result(j)(permutation(j)) = None
    }

    result
  }

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    val sqrt_dim = c.parameter("sqrt_dim").toPositiveInteger
    val copies = c.parameter("copies").toPositiveInteger

    solved_puzzle = prepareSolvedPuzzle(sqrt_dim)

    puzzles = new Array[ Array[Array[Option[Int]]] ](copies)
    for (c <- 0 until copies) {
      puzzles(c) = preparePuzzleWithAFewHoles(solved_puzzle)
    }
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val sqrt_dim = c.parameter("sqrt_dim").toPositiveInteger
    val copies = c.parameter("copies").toPositiveInteger
    val threads = c.parameter("threads").toPositiveInteger
    val kill_after_seconds = c.parameter("kill_after_seconds").toPositiveInteger

    val results: Array[BenchmarkResult] = new Array[BenchmarkResult](copies)

    val executor: ExecutorService = Executors.newFixedThreadPool(threads)
    for (i <- 0 until copies) {
      val fi = i
      executor.submit(() => {
        results(fi) = new DokuResult(Solver.solve(puzzles(i), sqrt_dim), solved_puzzle)
        null
      })
    }
    executor.shutdown()

    try {
      if (!executor.awaitTermination(kill_after_seconds, TimeUnit.SECONDS)) {
        executor.shutdownNow()
        throw new InterruptedException("scala-doku computation took too long; terminating.")
      }
    } catch {
      case e: InterruptedException => {
        throw e
      }
      case e: Throwable => {
        executor.shutdownNow()
        throw new Exception("Unexpected exception occured in scala-doku.", e)
      }
    }

    Validators.compound(results:_*)
  }

  final class DokuResult(actual: Option[Array[Array[Int]]], expected: Array[Array[Int]])
    extends BenchmarkResult {

    override def validate(): Unit = {
      if (actual.isEmpty) {
        throw new ValidationException("Result array does not exist.")
      }

      for ((expectedSlice, index) <- expected.zipWithIndex) {
        val actualSlice = actual.get(index)
        if (!expectedSlice.sameElements(actualSlice)) {
          throw new ValidationException(
            s"Result row $index does not match the expected solution: actual ${actualSlice.toSeq}, expected ${expectedSlice.toSeq}"
          )
        }
      }
    }
  }

}
