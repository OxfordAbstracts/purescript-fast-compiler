import { Faker } from '@faker-js/faker';

export const makeFakerImpl = (locale, seed) => new Faker({ locale, seed })
