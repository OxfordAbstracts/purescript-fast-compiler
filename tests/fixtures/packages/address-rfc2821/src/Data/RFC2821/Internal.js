import { Address } from 'address-rfc2821';

const makeAddressImpl = Left => Right => email => {
  try {
    return new Right(new Address(email));
  }
  catch(e) { return Left(e); }
}

export { makeAddressImpl };
