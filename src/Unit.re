let component = ReasonReact.statelessComponent("Unit");

let make = _children => {
  ...component,
  render: _self =>
    <div>
      (ReasonReact.string("<>"))
    </div>
};
