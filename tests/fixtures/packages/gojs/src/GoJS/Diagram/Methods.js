export const addNodeTemplate_ = (name) => (nodeTemplate) => (diag) => () => {
    diag.nodeTemplateMap.add(name, nodeTemplate);
}
export const addLinkTemplate_ = (name) => (linkTemplate) => (diag) => () => {
    diag.linkTemplateMap.add(name, linkTemplate);
}
export const addGroupTemplate_ = (name) => (groupTemplate) => (diag) => () => {
    diag.groupTemplateMap.add(name, groupTemplate);
}
