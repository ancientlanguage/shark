let component = ReasonReact.statelessComponent("TypeUnit");

let make = _children => {
  ...component,
  render: _self =>
    <div>
      (ReasonReact.string("<>"))
    </div>
};
