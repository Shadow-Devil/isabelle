/*  Title:      HOL/Tools/ATP/system_on_tptp.scala
    Author:     Makarius

Support for remote ATPs via SystemOnTPTP.
*/

package isabelle.atp

import isabelle._

import java.net.URL


object SystemOnTPTP
{
  /* requests */

  def get_url(options: Options): URL = Url(options.string("SystemOnTPTP"))

  def post_request(url: URL, parameters: List[(String, Any)]): HTTP.Content =
  {
    val parameters0 =
      List("NoHTML" -> 1, "QuietFlag" -> "-q0")
        .filterNot(p0 => parameters.exists(p => p0._1 == p._1))
    HTTP.Client.post(url, parameters0 ::: parameters, user_agent = "Sledgehammer")
  }


  /* list systems */

  def proper_lines(content: HTTP.Content): List[String] =
    Library.trim_split_lines(content.text).filterNot(_.startsWith("%"))

  def list_systems(url: URL): List[String] =
    proper_lines(post_request(url, List("SubmitButton" -> "ListSystems", "ListStatus" -> "READY")))

  object List_Systems extends Scala.Fun("SystemOnTPTP.list_systems", thread = true)
  {
    val here = Scala_Project.here
    def apply(url: String): String = cat_lines(list_systems(Url(url)))
  }
}
