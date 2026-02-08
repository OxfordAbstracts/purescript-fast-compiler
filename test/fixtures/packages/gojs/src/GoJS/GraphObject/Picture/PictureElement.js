
export const whichPictureElementStr = (x) => {
    if (x instanceof HTMLCanvasElement){
        return "canvas";
    } else if (x instanceof HTMLVideoElement){
        return "video";
    } else if (x instanceof HTMLImageElement){
        return "image";
    } else {
        return "unknown";
    }
}