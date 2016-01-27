/**
  * Created by Maximova on 27.01.2016.
  */
sealed abstract class Program
  case class Var(name: String)
  case class Const()
  case class Fun(component: Component, args: List[Program])
