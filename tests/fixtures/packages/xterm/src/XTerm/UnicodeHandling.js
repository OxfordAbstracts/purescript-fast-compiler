export const registerVersionProvider u => v => () => 
  u.register({ version: v.version, wcwidth: v.wcwidth, charProperties: (c,p) => v.charProperties(c,p) });
export const registeredVersions = u => () => u.versions; 
export const getActiveVersion = u => () => u.activeVersion;
export const setActiveVersion = u => s => () => u.activeVersion = s;
