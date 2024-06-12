open! Core

let () = Py.initialize ()

let draw ~plot_path ~title ~samples ~num_samples =
  let m = Py.Import.add_module "ocaml" in
  List.iter2_exn ~f:(Py.Module.set m)
    [ "plot_path"; "title"; "samples"; "num_samples" ]
    [
      Py.String.of_string plot_path;
      Py.String.of_string title;
      Py.Array.numpy samples;
      Py.Int.of_int num_samples;
    ];

  Py.Run.eval ~start:Py.File
    {|
from ocaml import plot_path, title, samples, num_samples
import seaborn as sns

sns.set_theme()

g = sns.displot(samples, element="step", stat="probability", bins=num_samples // 1500)
g.set_titles(title)
g.tight_layout()
g.savefig(plot_path) |}
  |> ignore
