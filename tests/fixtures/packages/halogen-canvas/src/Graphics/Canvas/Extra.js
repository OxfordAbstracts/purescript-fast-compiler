export const _newOffScreenCanvas = w => h => () => {
  return new OffscreenCanvas(w, h);
}

export const _convertToJpegBlob = canvas => quality => () => {
  return canvas.convertToBlob( { type: "image/jpeg", quality: quality }); 
}

export const canvasImageSourceWidth = (img) => {
  return img.width;
}

export const canvasImageSourceHeight = (img) => {
  return img.height;
}


