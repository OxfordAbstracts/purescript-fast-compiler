export const devicePixelRatioImpl = () => window.devicePixelRatio;

export const matchMedia = mediaQueryString => () =>
  window.matchMedia(mediaQueryString);
