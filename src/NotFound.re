open Utils;

requireCSS("src/NotFound.css");

let component = ReasonReact.statelessComponent("NotFound");

let make = _children => {
  ...component,
  render: _self =>
    <div className="NotFound_container">
      <div className="NotFound_text">
        <span>
          (
            ReasonReact.string(
              "Page not found. ",
            )
          )
        </span>
        <Link href="/"> (ReasonReact.string("Click here")) </Link>
      </div>
    </div>,
};
