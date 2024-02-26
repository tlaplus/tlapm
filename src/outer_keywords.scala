// DESCRIPTION: print outer syntax keywords of specified theory
//
// INSTALLATION:
// Place this Scala script in the directory $ISABELLE_HOME_USER/Tools
// and to the file $ISABELLE_HOME_USER/etc/settings the line
// ISABELLE_TOOLS="$ISABELLE_TOOLS:$ISABELLE_HOME_USER/Tools"
// To find the path ISABELLE_HOME_USER the tool `isabelle getenv` can be used
// by invoking:
//     isabelle getenv ISABELLE_HOME_USER
// For example, when this script was first used for `tlapm`, this path was
//     $HOME/.isabelle/Isabelle2021-RC2
//
// Invoke the script with:
//     isabelle outer_keywords Pure

object Tool extends isabelle.Isabelle_Tool.Body {
  import isabelle._

  def outer_keywords(
    options: Options,
    theory_name: String,
    dirs: List[Path] = Nil,
    progress: Progress = new Progress)
  {
    val sessions_structure = Sessions.load_structure(options, dirs = dirs)
    val session_name = sessions_structure.bootstrap.theory_qualifier(theory_name)
    val deps = Sessions.deps(sessions_structure.selection(session_name))

    deps(session_name).loaded_theory_syntax(theory_name) match {
      case None => error("Bad theory " + quote(theory_name))
      case Some(syntax) =>
        val keywords = syntax.keywords.kinds.keySet.toList.sorted
        keywords.foreach(progress.echo)
    }
  }

  def apply(args: List[String])
  {
    var dirs: List[Path] = Nil

    val getopts = Getopts("""
Usage: isabelle outer_keywords [OPTIONS] THEORY

  Options are:
    -d DIR       include session directory

  Print outer syntax keywords of specific theory (long name), e.g.
  "Pure", "Main", "HOL-Library.Multiset".
""",
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))))

    val more_args = getopts(args)
    val theory_name =
      more_args match {
        case List(name) => name
        case _ => getopts.usage()
      }

    val options = Options.init()
    val progress = new Console_Progress()

    outer_keywords(options, theory_name, dirs = dirs, progress = progress)
  }
}
