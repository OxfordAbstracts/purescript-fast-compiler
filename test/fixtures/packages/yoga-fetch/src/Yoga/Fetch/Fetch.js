export const _fetch = fetchImpl => url => options => () => {
        return fetchImpl(url, options).catch(function(e) {
          // we have to wrap node-fetch's non-Error error :(
          throw new Error(e);
        });
};

export const jsonImpl = response => () => {
    return response.json().catch(function(e) {
      throw new Error(e);
    });
};

export const textImpl = response => () => response.text()

export const headersImpl = response => {
  var result = {};
  for (const [key, value] of response.headers.entries()) {
    result[key] = value
  }
  return result;
};


export const arrayBufferImpl = response => () => response.arrayBuffer()
