import * as go from 'gojs';

export const newButton = (buttonType) => (buttonPanelType) => () => {
    return go.GraphObject.make(buttonType + "Button", buttonPanelType);
}
export const newContextMenu = () => {
    return go.GraphObject.make("ContextMenu");
}

export const newToolTip = () => {
    return go.GraphObject.make("ToolTip");
}
