import { HasInitializer } from './all.mjs';

export function ExpectedArgumentCount(FormalParameterList) {
  if (FormalParameterList.length === 0) {
    return 0;
  }

  let count = 0;
  const lastIndex = FormalParameterList.length - 1;
  while (count < lastIndex) {
    const BindingElement = FormalParameterList[count];
    if (HasInitializer(BindingElement)) {
      return count;
    }
    count += 1;
  }

  const last = FormalParameterList[lastIndex];
  if (last.type === 'BindingRestElement' || HasInitializer(last)) {
    return count;
  }
  return count + 1;
}
