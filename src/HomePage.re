type state = Type.shark;

type action =
  | ChangeType;

let reducer = (action, _state) =>
  switch (action) {
  | ChangeType => ReasonReact.Update(Type.Unit)
  };

let component = ReasonReact.reducerComponent("HomePage");

let make = _children => {
  ...component,
  reducer,
  initialState: () => Type.Or([| Type.Unit, Type.Unit, Type.Unit, |]),
  render: self =>
    switch (self.state) {
    | Type.Unit => <TypeUnit />
    | Type.Or(orChildren) => <TypeOr orChildren />
    | Type.And(_) => <div>(ReasonReact.string("And!"))</div>
    | Type.Array(_) => <div>(ReasonReact.string("Array!"))</div>
    },
};
