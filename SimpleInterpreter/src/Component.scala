/**
  * Created by Maximova on 27.01.2016.
  */
abstract class Component {
  val name: String
  val arity: Int
  def eval(args: List[Any])
}
