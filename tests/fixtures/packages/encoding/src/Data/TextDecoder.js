export function decodeImpl (Left, Right, label, buffer) {
  let result;
  const decoder = new TextDecoder(label, { fatal: true });

  try {
    result = Right(decoder.decode(buffer));
  }
  catch (error) {
    result = Left(error);
  }

  return result;
};
