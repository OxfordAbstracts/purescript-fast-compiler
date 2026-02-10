
export const whichBrushPatternStr = (x) => {
    if (x instanceof HTMLCanvasElement){
        return "canvas";
    } else if (x instanceof HTMLImageElement){
        return "image";
    } else {
        return "unknown";
    }
}