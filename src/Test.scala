package pp201701.projtest
import pp201701.proj.Main._
import pp201701.proj.Value._
import pp201701.proj.Data.DataBundle._
import pp201701.proj.Data.DataBundle.ExprToString._
import pp201701.proj.Lexer._
import pp201701.proj.Parser._

object Test extends App {
  def print_result(b:Boolean) : Unit =
    if (b) println("O") else println("X")

  def run_eval(eval: Expr => Val)(code:String) : Val = {
    val tokens = ProjLexer(code)
    val e:Expr = Parser(tokens)
    eval(e)
  }

  def run_myeval = run_eval(myeval) _
  def run_myeval_memo = run_eval(myeval_memo) _

  def run_test(implicit conv:ConvertToScala[Val]) = {
    try {
      println("=================")
      println("1. Basic Test")

      { // 1
      val code = "(hd (cons 1 2))"
        val res = conv.toInt(run_myeval(code)) match {
          case Some(1) => true
          case _ => false
        }
        print_result(res)
      }

      { // 2
      val code = "(let ((val p (cons 1 (cons true nil)))) (cons 0 p))"
        val res = conv.toPair(run_myeval(code)) match {
          case Some(_) => true // this only checks whether the result is a pair.
          case _ => false
        }
        print_result(res)
      }

      { // 3
      val code = "(if true 10 20)"
        val res = conv.toInt(run_myeval(code)) match {
          case Some(10) => true
          case _ => false
        }
        print_result(res)
      }

      { // 4
      val code = "((fun (x y) (+ x y)) 1 2)"
        val res = conv.toInt(run_myeval(code)) match {
          case Some(3) => true
          case _ => false
        }
        print_result(res)
      }

      { // 5
      val code = "(let ((val f (fun () (+ 1 2)) )) (f))"
        val res = conv.toInt(run_myeval(code)) match {
          case Some(3) => true
          case _ =>  ; false
        }
        print_result(res)
      }

      { // 6
      val code = "(let ((val a 10) (val b (+ a 1))) (* b 3))"
        val res = conv.toInt(run_myeval(code)) match {
          case Some(33) => true
          case _ => false
        }
        print_result(res)
      }

      { // 7
      val code = "(let ((def f (fun (x) (if (= x 0) 0 (+ x (f (- x 1))))))) (f 5))"
        val res = conv.toInt(run_myeval(code)) match {
          case Some(15) => true
          case _ => false
        }
        print_result(res)
      }

      { // 8
      val code = "(let ((def f (fun (n) (g n 1))) (def g (fun (a b) (> a b)))) (f 3))"
        val res = conv.toBool(run_myeval(code)) match {
          case Some(true) => true
          case _ => false
        }
        print_result(res)
      }

      { // 9
      val code = "((fun (f) (fun (x) (f x))) (fun (x) (+ x 1)))"
        val res = conv.isFun(run_myeval(code)) match {
          case true => true
          case _ => false
        }
        print_result(res)
      }
    } catch {
      case e : LexerException =>
        println("Lexer failed: " + e.msg)
      case e : ParserException =>
        println("Parser failed: " + e.msg)
      case e : EvalException =>
        println("myeval failed: " + e.msg)
    }

    try {
//      println("=================")
//      println("2. Tailrec Test (should be finished)")
//      val code = "(let ((def f (fun (x n) (if (= x 0) n (f (- x 1) (+ n x)))) )) (f 9999 0))"
//      val res = conv.toInt(run_myeval(code)) match {
//        case Some(49995000) => true
//        case _ => false
//      }
//      print_result(res)
    } catch {
      case e : LexerException =>
        println("Lexer failed: " + e.msg)
      case e : ParserException =>
        println("Parser failed: " + e.msg)
      case e : EvalException =>
        println("myeval failed: " + e.msg)
    }

    try {
      println("=================")
      println("3. Memoization Test (should take less than 5 sec)")
      val code = "(let ((def f (fun (n) (if (= n 0) 1 (if (= n 1) 0 (if (> (f (- n 1)) (f (- n 2))) 0 1)))))) (f 100))"
      val res = conv.toInt(run_myeval_memo(code)) match {
        case Some(1) => true
        case _ => false
      }
      print_result(res)
    } catch {
      case e : LexerException =>
        println("Lexer failed: " + e.msg)
      case e : ParserException =>
        println("Parser failed: " + e.msg)
      case e : EvalException =>
        println("myeval failed: " + e.msg)
    }
  }

  run_test
}