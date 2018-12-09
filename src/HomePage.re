type sharkType =
  | Unit
  | Or(list(sharkType))
  | And(list(sharkType))
  | Array(sharkType, sharkType); /* first ^ second */

type state = sharkType;

type action =
  | ChangeType;

let reducer = (action, _state) =>
  switch (action) {
  | ChangeType => ReasonReact.Update(Unit)
  };

let component = ReasonReact.reducerComponent("HomePage");

let make = _children => {
  ...component,
  reducer,
  initialState: () => Unit,
  render: self =>
    switch (self.state) {
    | Unit => <Unit />
    | Or(_) => <div>(ReasonReact.string("Or!"))</div>
    | And(_) => <div>(ReasonReact.string("And!"))</div>
    | Array(_) => <div>(ReasonReact.string("Array!"))</div>
    },
};
