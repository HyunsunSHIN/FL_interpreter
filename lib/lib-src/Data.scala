package pp201701.proj.Data

object DataBundle {

  sealed abstract class Const
  case class CInt(n:Int) extends Const
  case class CTrue() extends Const
  case class CFalse() extends Const
  case class CNil() extends Const

  sealed abstract class Expr
  case class EConst(c:Const) extends Expr //
  case class EName(x:String) extends Expr//
  case class EIf(econd:Expr, et:Expr, ef:Expr) extends Expr //
  case class ECons(eh:Expr, et:Expr) extends Expr //
  case class EHd(el:Expr) extends Expr //
  case class ETl(el:Expr) extends Expr //

  case class EFun(params:List[String], eb:Expr) extends Expr
  case class EApp(ef:Expr, eargs:List[Expr]) extends Expr

  case class ELet(bs:List[Bind], eb:Expr) extends Expr

  case class EPlus(e1:Expr, e2:Expr) extends Expr //
  case class EMinus(e1:Expr, e2:Expr) extends Expr//
  case class EMult(e1:Expr, e2:Expr) extends Expr//
  case class EEq(e1:Expr, e2:Expr) extends Expr//
  case class ELt(e1:Expr, e2:Expr) extends Expr//
  case class EGt(e1:Expr, e2:Expr) extends Expr//

  sealed abstract class BKind
  case class BDEF() extends BKind
  case class BVAL() extends BKind

  type Bind = (BKind, String, Expr)

  object ExprToString {

    def const_toString (c:Const) : String =
      c match {
        case CInt(n) => n.toString
        case CTrue() => "true"
        case CFalse() => "false"
        case CNil() => "nil"
      }

    def concat(sl:List[String]) : String = {
      def cc_intl(l:List[String]):String =
        l match {
          case Nil => ""
          case h::t => " " + h + cc_intl(t)
        }
      sl match {
        case Nil => ""
        case h::t => h + cc_intl(t)
      }
    }

    def inparen(s:String):String = "(" + s + ")"

    def expr_toString (e:Expr) : String =
      e match {

        case EConst(c) => const_toString(c)
        case EName(x) => x
        case EIf(e1, e2, e3) => inparen(concat(List("if", expr_toString(e1), expr_toString(e2), expr_toString(e3))))
        case ECons(e1, e2) => inparen(concat(List("cons", expr_toString(e1), expr_toString(e2))))
        case EHd(e1) => inparen(concat(List("hd", expr_toString(e1))))
        case ETl(e1) => inparen(concat(List("tl", expr_toString(e1))))

        case EFun(p, e1) => {
          val sp = inparen(concat(p))
          inparen(concat(List("fun", sp, expr_toString(e1))))
        }
        case EApp(e1, el) => {
          inparen(expr_toString_list(e1::el))
        }
        case ELet(b, e1) => {
          val sl = inparen(binds_toString(b))
          inparen(concat(List("let", sl, expr_toString(e1))))
        }
        case EPlus(e1, e2) => //
          inparen(concat(List("+", expr_toString(e1), expr_toString(e2))))
        case EMinus(e1, e2) => //
          inparen(concat(List("-", expr_toString(e1), expr_toString(e2))))
        case EMult(e1, e2) => //
          inparen(concat(List("*", expr_toString(e1), expr_toString(e2))))
        case EEq(e1, e2) => //
          inparen(concat(List("=", expr_toString(e1), expr_toString(e2))))
        case ELt(e1, e2) => //
          inparen(concat(List("<", expr_toString(e1), expr_toString(e2))))
        case EGt(e1, e2) => //
          inparen(concat(List(">", expr_toString(e1), expr_toString(e2))))
      }

    def expr_toString_list(el:List[Expr]):String =
      concat(el.map(expr_toString))
    def binds_toString(bl:List[Bind]) : String = {

      def bkind_toString(k:BKind) : String =
        k match {
          case BVAL() => "val"
          case BDEF() => "def"
        }
      def bind_toString(b:Bind):String =
        inparen(concat(List(bkind_toString(b._1), b._2,
          expr_toString(b._3))))

      concat(bl.map(bind_toString))
    }
  }

}
