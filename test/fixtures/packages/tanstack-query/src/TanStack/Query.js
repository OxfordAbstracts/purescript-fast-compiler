import {
    useQuery,
    useMutation,
    useQueryClient,
    QueryClient,
    QueryClientProvider,
} from '@tanstack/react-query'

export const useQueryImpl = useQuery
export const useMutationImpl = useMutation
export const useQueryClientImpl = useQueryClient

export const newQueryClient = () => new QueryClient()
export const queryClientProviderImpl = QueryClientProvider

export const invalidateQueries = args => client => () => client.invalidateQueries(args)

export const getQueryDataImpl = args => client => () => client.getQueryData(args)
export const setQueryDataImpl = (args, data, client) => client.setQueryData(args, data)