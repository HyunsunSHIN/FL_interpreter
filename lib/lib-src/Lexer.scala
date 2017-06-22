package pp201701.proj.Lexer

import scala.util.parsing._
import scala.util.parsing.combinator._
import pp201701.proj.Data.DataBundle._

class LexerException(val msg: String) extends Exception

sealed trait Token

case class TINT(n:Int) extends Token
case class TTRUE() extends Token
case class TFALSE() extends Token
case class TNIL() extends Token

case class TNAME(str:String) extends Token

case class TIF() extends Token
case class TCONS() extends Token
case class THD() extends Token
case class TTL() extends Token
case class TFUN() extends Token
case class TLET() extends Token

case class TDEF() extends Token
case class TVAL() extends Token

case class TPLUS() extends Token
case class TMINUS() extends Token
case class TMULT() extends Token
case class TEQ() extends Token
case class TLT() extends Token
case class TGT() extends Token

case class TLPAREN() extends Token
case class TRPAREN() extends Token

object ProjLexer extends RegexParsers {
  override def skipWhitespace = true
  override val whiteSpace = "[ \t\r\f\n]+".r

  def tint: Parser[TINT] = {
    """(0|[1-9]\d*)""".r ^^ { n => TINT(n.toInt) }
  }
  def ttrue: Parser[TTRUE] = {
    "true" ^^ { _ => TTRUE() }
  }
  def tfalse: Parser[TFALSE] = {
    "false" ^^ { _ => TFALSE() }
  }
  def tnil: Parser[TNIL] = {
    "nil" ^^ { _ => TNIL() }
  }

  def tname: Parser[TNAME] = {
    "[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { str => TNAME(str) }
  }

  def tif: Parser[TIF] = {
    "if" ^^ { _ => TIF() }
  }
  def tcons: Parser[TCONS] = {
    "cons" ^^ { _ => TCONS() }
  }
  def thd: Parser[THD] = {
    "hd" ^^ { _ => THD() }
  }
  def ttl: Parser[TTL] = {
    "tl" ^^ { _ => TTL() }
  }
  def tfun: Parser[TFUN] = {
    "fun" ^^ { _ => TFUN() }
  }
  def tlet: Parser[TLET] = {
    "let" ^^ { _ => TLET() }
  }
  def tdef: Parser[TDEF] = {
    "def" ^^ { _ => TDEF() }
  }
  def tval: Parser[TVAL] = {
    "val" ^^ { _ => TVAL() }
  }

  def tplus: Parser[TPLUS] = {
    "+" ^^ { _ => TPLUS() }
  }
  def tminus: Parser[TMINUS] = {
    "-" ^^ { _ => TMINUS() }
  }
  def tmult: Parser[TMULT] = {
    "*" ^^ { _ => TMULT() }
  }
  def teq: Parser[TEQ] = {
    "=" ^^ { _ => TEQ() }
  }
  def tlt: Parser[TLT] = {
    "<" ^^ { _ => TLT() }
  }
  def tgt: Parser[TGT] = {
    ">" ^^ { _ => TGT() }
  }

  def tlparen: Parser[TLPAREN] = {
    "(" ^^ { _ => TLPAREN() }
  }
  def trparen: Parser[TRPAREN] = {
    ")" ^^ { _ => TRPAREN() }
  }

  def tokens: Parser[List[Token]] = {
    phrase(rep1(tint|ttrue|tfalse|tnil|
      tif|tcons|thd|ttl|tfun|tlet|tdef|tval|
      tplus|tminus|tmult|teq|tlt|tgt|tlparen|trparen|
      tname)) ^^ { t => t }
  }

  def apply(code: String): List[Token] = {
    parse(tokens, code) match {
      case NoSuccess(msg, next) => throw new LexerException(msg)
      case Success(result, next) => result
        // 여기서 apply는 Lexer.scala에서 정의한 토큰들과 함께,
        // parsing의 대상이 되는 코드들을 전달하면,
        // Token들의 list로 바꿔준다 => 여기서 Token은 algebraic 데이터 타입이기 때문에
        // 나중에 이 값들을 pattern matching 로 할 수 있다.

    }
  }
}
