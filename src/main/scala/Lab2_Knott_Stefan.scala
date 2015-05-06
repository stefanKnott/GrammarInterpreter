object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
   * Stefan Knott
   * 
   * Partner: Jake Levine
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /* We represent a variable environment is as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(true) => 1.0
      case B(false) => 0.0
      case Undefined => Double.NaN
      case S(s) => try s.toDouble catch{ case _: Throwable => Double.NaN}
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      //needed to check for NaN as well as 0!
      case N(n) => if(n.isNaN()) false else if((n compare(0.0)) == 0) false else if ((n compare(-0.0)) == 0) false else true
      case S(s) => if( s == "") false else true
      case Undefined => false
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => if(n.isWhole) "%.0f" format n else n.toString
      case S(s) => s
      case B(false) => "false"
      case B(true) => "true"
      case Undefined => "undefined"
   //   case Function(_,_,_) => "function"
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)

    def isEqual(e1: Expr, e2: Expr): Boolean = (e1, e2) match {
      case (N(a), N(b)) => (a == b)
      case (B(a),B(b)) => (a == b)
      case (S(a),S(b)) => (a == b)
      case (Undefined,Undefined) => true
      case _ => false
    }

    e match {
      case B(_) | N(_) | S(_)| Undefined => e
     
      case Unary(uop: Uop, e1: Expr)=> uop match{
          case Neg => return N(-toNumber(eToVal(e1)))
          case Not => return B(!toBoolean(eToVal(e1)))
          case _ => throw new UnsupportedOperationException
        }

      case Binary(bop: Bop, e1: Expr, e2: Expr) => bop match{
        case Eq => B(isEqual(eToVal(e1), eToVal(e2)))

        //Check for arithmetic, or string concatenation
        case Plus => 
          val ax = eToVal(e1)
          val bx = eToVal(e2)
          (ax, bx) match {
            case (S(a), b) => S(a + toStr(b))
            case (a, S(b)) => S(toStr(a) + b)
            case(B(a), b) => eval(env, Binary(Plus, N(toNumber(e1)), e2))
            case(a, B(b)) => eval(env, Binary(Plus, e1, N(toNumber(e2))))
            case _ => N(toNumber(ax) + toNumber(bx))
          }
        
        case Minus => N(toNumber(eToVal(e1)) - toNumber(eToVal(e2)))
        case Times => N(toNumber(eToVal(e1)) * toNumber(eToVal(e2)))
        case Div => {
                      if(toNumber(eToVal(e2)) == 0) {
                        if(toNumber(eToVal(e1)) > 0){
                          N(Double.PositiveInfinity)
                          }
                          else{N(Double.NegativeInfinity)}
                        }
                      else N(toNumber(eToVal(e1)) / toNumber(eToVal(e2)))
                    }

        
        case Lt => eval(env, e1) match{
            case S(a) => eval(env, e2) match{
                case S(b) => if(a.charAt(0).toInt < b.charAt(0).toInt) return B(true) else return B(false)
                case _ => B(toNumber(eToVal(e1)) < toNumber(eToVal(e2)))
            }
            case _ => B(toNumber(eToVal(e1)) < toNumber(eToVal(e2)))
          }

        case Gt =>  B(toNumber(eToVal(e1)) > toNumber(eToVal(e2)))
        case Le => B(toNumber(eToVal(e1)) <= toNumber(eToVal(e2)))
        case Ge => B(toNumber(eToVal(e1)) >= toNumber(eToVal(e2)))
        case Ne => B(!isEqual(eToVal(e1), eToVal(e2)))

        //case match for booleans and for any other type, return the 2nd variable in the and operation
        case And => 
          val ax = eToVal(e1)
          val bx = eToVal(e2)
          (ax, bx) match {
            case(B(a), B(b)) => B(a && b)

            case (a, b) => eToVal(b)
          }
        
        case Or => var x = eToVal(e1)
                    if(toBoolean(x)) x else eToVal(e2)
        case Seq => eval(env, e1)
                    eval(env, e2)
        case _ => throw new UnsupportedOperationException

      }
      
      case If(cond: Expr, a: Expr, b: Expr) =>  if(toBoolean(cond)) eval(a) else eval(b)
     
      case Var(x) => eToVal(get(env, x))
      case ConstDecl(x, e1, e2) => {
        val envp = extend(env, x, eToVal(e1))
        eval(envp, e2)
      }

      /* Inductive Cases */

      case Print(e1) => println(pretty(eToVal(e1))); Undefined

      case _ => throw new UnsupportedOperationException
    }
  }
    
  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = {
  //  println(e)
    eval(emp, e)
  }
  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

 /* Interface to run your interpreter from the command-line.  You can ignore what's below. */ 
 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }
    
    val v = eval(expr)
    
    println(pretty(v))
  }

}