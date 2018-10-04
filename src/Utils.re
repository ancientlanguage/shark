/* require css file for side effect only */
[@bs.val] external requireCSS : string => unit = "require";

/* require an asset (eg. an image) and return exported string value (image URI) */
[@bs.val] external requireAssetURI : string => string = "require";

[@bs.send] [@bs.return nullable]
external getAttribute : (Js.t('a), string) => option(string) =
  "getAttribute";

[@bs.module]
external registerServiceWorker : unit => unit = "src/registerServiceWorker";
