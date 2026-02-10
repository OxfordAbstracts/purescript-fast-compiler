import url from "node:url";

export const newImpl = (input) => new url.URL(input);
export const newRelativeImpl = (input, base) => new url.URL(input, base);
export const pathToFileURLImpl = (path) => url.pathToFileURL(path);
export const hashImpl = (u) => u.hash;
export const setHashImpl = (h, u) => {
  u.hash = h;
};
export const hostImpl = (url) => url.host;
export const setHostImpl = (val, u) => {
  u.host = val;
};
export const hostnameImpl = (u) => u.hostname;
export const setHostnameImpl = (val, u) => {
  u.hostname = val;
};
export const hrefPure = (u) => u.href;
export const hrefImpl = (u) => u.href;
export const setHrefImpl = (val, u) => {
  u.href = val;
};
export const origin = (u) => u.origin;
export const passwordImpl = (u) => u.password;
export const setPasswordImpl = (val, u) => {
  u.password = val;
};
export const pathnameImpl = (u) => u.pathname;
export const setPathnameImpl = (val, u) => {
  u.pathname = val;
};
export const portImpl = (u) => u.port;
export const setPortImpl = (val, u) => {
  u.port = val;
};
export const protocolImpl = (u) => u.protocol;
export const setProtocolImpl = (val, u) => {
  u.protocol = val;
};
export const searchImpl = (u) => u.search;
export const setSearchImpl = (val, u) => {
  u.search = val;
};
export const searchParamsImpl = (u) => u.searchParams;
export const usernameImpl = (u) => u.username;
export const setUsernameImpl = (val, u) => {
  u.username = val;
};

export const canParseImpl = (input, base) => url.URL.canParse(input, base);
export const domainToAsciiImpl = (domain) => url.domainToASCII(domain);
export const domainToUnicodeImpl = (domain) => url.domainToUnicode(domain);
export const fileURLToPathImpl = (str) => url.fileURLToPath(str);
export const fileURLToPathUrlImpl = (str) => url.fileURLToPath(str);
export const formatImpl = (theUrl) => url.format(theUrl);
export const formatOptsImpl = (theUrl, opts) => url.format(theUrl, opts);
export const pathToFileUrlImpl = (path) => url.pathToFileURL(path);
export const urlToHttpOptionsImpl = (theUrl) => url.urlToHttpOptions(theUrl);
