using JuMP

vis_pos(x) = x[x .> 1e-5]

var_name_to_tuple = (x) -> (map(y -> parse(Int, y), split(split(x, ')')[1][3:end], ','))...,)

function read_objective_from_lp_file(path, tuple_lookup_index)
    # index of Minimize line
    lines = readlines(path)
    start = findfirst(x -> x == "Minimize", lines)
    # index of Subject To
    stop = findfirst(x -> x == "Subject To", lines)
    content = lines[(start+1):(stop-1)]
    # remove "obj:" from the first line
    content[1] = replace(content[1], "obj: "=> "")

    # split by whitespace and flatten
    content = vcat(split.(content, r"\s+")...) |> filter(x -> x != "")

    if content[1] != "-"
        content = ["+" content...]
    end

    @show content

    # group by 3
    content = [content[i:i+2] for i in 1:3:length(content)]

    J, K = Int[], Float64[]
    for (sign, valstr, varname) in content
        tuple = var_name_to_tuple(varname)
        val = parse(Float64, valstr)
        if sign == "-"
            val = -val
        end
        # @show tuple
        # val = parse(Float64, valstr)
        # idx = tuple_lookup_index[varname]
        push!(K, val)
        push!(J, tuple_lookup_index[tuple])
    end

    return sparse(ones(length(J)), J, K, 1, length(tuple_lookup_index))

    # lines[1] =  lines[1]
    # @show content

end


function read_qap_weights_file(path)
    lines = readlines(path)
    n = parse(Int, lines[1])
    D_lines = lines[3:(n+2)]
    E_lines = lines[(n+4):(2*n+3)]
    C_lines = lines[(2*n+5):end]

    parse_mat(lines) = hcat([parse.(Float64, split(line, ",")) for line in lines]...)'

    parse_mat(D_lines), parse_mat(E_lines), parse_mat(C_lines)
end

function write_qap_weights_file(D, E, C, path)
    n = size(D, 1)
    D_lines = ["$n", "", join([join(string.(x), ',') for x in eachcol(D')], "\n")]
    E_lines = ["", join([join(string.(x), ',') for x in eachcol(E')], "\n")]
    C_lines = ["", join([join(string.(x), ',') for x in eachcol(C')], "\n")]
    lines = [D_lines; E_lines; C_lines]
    write(path, join(lines, "\n"))
end

function write_tsp_weights_file(w, path)
    sz = round(Int, sqrt(length(w)))
    @assert sz*(sz-1) == length(w)
    mat = similar(w, sz, sz)
    for i in 1:sz
        mat[i, i] = 0
        for j in 1:(sz-1)
            adjusted_j = j + (j >= i)
            mat[i, adjusted_j] = w[(i-1)*(sz-1) + j]
        end
    end  

    lines = [
        "$sz";
        "";
        [join(string.(x), ',') for x in eachcol(mat)]...
    ]
    write(path, join(lines, "\n"))
end

function _standard_form_matrix(model::Model)
    columns = Dict(var => i for (i, var) in enumerate(all_variables(model)))
    n = length(columns)
    c_l, c_u = fill(-Inf, n), fill(Inf, n)
    r_l, r_u = Float64[], Float64[]
    I, J, V = Int[], Int[], Float64[]
    bound_constraints = ConstraintRef[]
    affine_constraints = ConstraintRef[]
    for (F, S) in list_of_constraint_types(model)
        _fill_standard_form(
            model,
            columns,
            bound_constraints,
            affine_constraints,
            F,
            S,
            c_l,
            c_u,
            r_l,
            r_u,
            I,
            J,
            V,
        )
    end

    num_constrs = length(r_l)

    for i in 1:n
        push!(I, num_constrs + i)
        push!(J, i)
        push!(V, 1.0)
    end



    return (
        columns=columns,
        lower=vcat(r_l, c_l),
        upper=vcat(r_u, c_u),
        A=SparseArrays.sparse(I, J, V, length(r_l) + n, n),
        bounds=bound_constraints,
        constraints=affine_constraints,
    )
end

function _fill_standard_form(
    model::Model,
    x::Dict{VariableRef,Int},
    bound_constraints::Vector{ConstraintRef},
    ::Vector{ConstraintRef},
    F::Type{VariableRef},
    S::Type,
    c_l::Vector{Float64},
    c_u::Vector{Float64},
    ::Vector{Float64},
    ::Vector{Float64},
    ::Vector{Int},
    ::Vector{Int},
    ::Vector{Float64},
)
    for c in all_constraints(model, F, S)
        push!(bound_constraints, c)
        c_obj = constraint_object(c)
        i = x[c_obj.func]
        set = MOI.Interval(c_obj.set)
        c_l[i] = max(c_l[i], set.lower)
        c_u[i] = min(c_u[i], set.upper)
    end
    return
end

function _fill_standard_form(
    model::Model,
    x::Dict{VariableRef,Int},
    ::Vector{ConstraintRef},
    affine_constraints::Vector{ConstraintRef},
    F::Type{<:GenericAffExpr},
    S::Type,
    ::Vector{Float64},
    ::Vector{Float64},
    r_l::Vector{Float64},
    r_u::Vector{Float64},
    I::Vector{Int},
    J::Vector{Int},
    V::Vector{Float64},
)
    for c in all_constraints(model, F, S)
        push!(affine_constraints, c)
        c_obj = constraint_object(c)
        @assert iszero(c_obj.func.constant)
        row = length(r_l) + 1
        set = MOI.Interval(c_obj.set)
        push!(r_l, set.lower)
        push!(r_u, set.upper)
        for (var, coef) in c_obj.func.terms
            push!(I, row)
            push!(J, x[var])
            push!(V, coef)
        end
        # push!(I, row)
        # push!(J, length(x) + row)
        # push!(V, -1.0)
    end
    return
end




function _standard_form_matrix2(model::Model)
    columns = Dict(var => i for (i, var) in enumerate(all_variables(model)))
    n = length(columns)
    c_l, c_u = fill(-Inf, n), fill(Inf, n)
    r_l, r_u = Float64[], Float64[]
    I, J, V = Int[], Int[], Float64[]
    bound_constraints = ConstraintRef[]
    affine_constraints = ConstraintRef[]
    for (F, S) in list_of_constraint_types(model)
        _fill_standard_form2(
            model,
            columns,
            bound_constraints,
            affine_constraints,
            F,
            S,
            c_l,
            c_u,
            r_l,
            r_u,
            I,
            J,
            V,
        )
    end
    return (
        columns = columns,
        lower = vcat(c_l, r_l),
        upper = vcat(c_u, r_u),
        A = SparseArrays.sparse(I, J, V, length(r_l), n + length(r_l)),
        bounds = bound_constraints,
        constraints = affine_constraints,
    )
end

function _fill_standard_form2(
    model::Model,
    x::Dict{VariableRef,Int},
    bound_constraints::Vector{ConstraintRef},
    ::Vector{ConstraintRef},
    F::Type{VariableRef},
    S::Type,
    c_l::Vector{Float64},
    c_u::Vector{Float64},
    ::Vector{Float64},
    ::Vector{Float64},
    ::Vector{Int},
    ::Vector{Int},
    ::Vector{Float64},
)
    for c in all_constraints(model, F, S)
        push!(bound_constraints, c)
        c_obj = constraint_object(c)
        i = x[c_obj.func]
        set = MOI.Interval(c_obj.set)
        c_l[i] = max(c_l[i], set.lower)
        c_u[i] = min(c_u[i], set.upper)
    end
    return
end

function _fill_standard_form2(
    model::Model,
    x::Dict{VariableRef,Int},
    ::Vector{ConstraintRef},
    affine_constraints::Vector{ConstraintRef},
    F::Type{<:GenericAffExpr},
    S::Type,
    ::Vector{Float64},
    ::Vector{Float64},
    r_l::Vector{Float64},
    r_u::Vector{Float64},
    I::Vector{Int},
    J::Vector{Int},
    V::Vector{Float64},
)
    for c in all_constraints(model, F, S)
        push!(affine_constraints, c)
        c_obj = constraint_object(c)
        @assert iszero(c_obj.func.constant)
        row = length(r_l) + 1
        set = MOI.Interval(c_obj.set)
        push!(r_l, set.lower)
        push!(r_u, set.upper)
        for (var, coef) in c_obj.func.terms
            push!(I, row)
            push!(J, x[var])
            push!(V, coef)
        end
        push!(I, row)
        push!(J, length(x) + row)
        push!(V, -1.0)
    end
    return
end


function lehmer_to_permutation(dec::Int, n::Int)
    dec -= 1
    # Step 1: Convert the index to Lehmer code
    lehmer_code = zeros(Int, n)

    product = 1
    iteration = 1
    for index in (n-2):-1:0
        product *= iteration
        iteration += 1

        divisor = dec ÷ product
        remainder = divisor % iteration

        lehmer_code[index+1] = remainder
    end

    sequence = collect(1:n)
    for (idx, d) in enumerate(lehmer_code)
        removed = popat!(sequence, d + 1)
        lehmer_code[idx] = removed
        # post_idx = d > idx ? idx : idx + 1

    end
    # increment by one to match julia
    # lehmer_code .+= 1

    return lehmer_code
end



function permutation_to_lehmer(permutation::Vector{Int})
    # convert indices to standard 0-based to make reasoning easier
    permutation = permutation .- 1

    n = length(permutation)
    lehmer_code = zeros(Int, n)
    for i in n:-1:1
        for j in (i+1):n
            if permutation[j] < permutation[i]
                lehmer_code[i] += 1
            end
        end
    end

    # Step 2: Convert the Lehmer code to index
    index = 0
    for i in 1:n
        index = index * (n - i + 1) + lehmer_code[i]
    end

    # increment by one to match julia
    index += 1
    return index
end


function compute_arcweight_to_cost_matrix_tsp(num_nodes)
    C = Dict{Tuple{Int,Int,Int,Int,Int,Int,Int},Int}()
    nnmo = num_nodes - 1
    function incr_C(x_idx_tuple, y_tuple, val)
        # remember that the 1d index skips diagonals so we can't just do the simple multiplication
        @assert y_tuple[1] != y_tuple[2]
        y_idx = y_tuple[1] * nnmo + y_tuple[2] - (y_tuple[1] < y_tuple[2]) + 1
        C[(x_idx_tuple..., y_idx)] = get(C, (x_idx_tuple..., y_idx), 0) + val
    end

    for i in 1:num_nodes-1
        for j in 1:num_nodes-1
            if i == j
                continue
            end
            for k in 1:num_nodes-1
                if k == i || k == j
                    continue
                end
                incr_C((i, 1, j, 2, k, 3), (0, i), 1)
                incr_C((i, 1, j, 2, k, 3), (i, j), 1)
                incr_C((i, 1, j, 2, k, 3), (j, k), 1)
                incr_C((i, 1, j, nnmo - 1, k, nnmo), (j, k), 1)
                incr_C((i, 1, j, nnmo - 1, k, nnmo), (k, 0), 1)

                for l in 4:nnmo-1
                    incr_C((i, 1, j, l - 1, k, l), (j, k), 1)
                end
            end
        end
    end
    C
end

function convert_a2c_dict_to_mat(h, var_idx_tuples, num_verts)
    var_idx_lookup = Dict(var_tuple => i for (i, var_tuple) in enumerate(var_idx_tuples))
    h_to_dict = Dict((idx[1:end-1], idx[end]) => val for (idx, val) in h)
    dst_mat = SparseArrays.spzeros(Bool, length(var_idx_tuples), num_verts * (num_verts - 1))
    for ((var_tuple, idx), val) in h_to_dict
        dst_mat[var_idx_lookup[var_tuple], idx] = val
    end
    dst_mat
end

extrema_dists(fsva, target=fsva) = Float64(dot(fsva, target)) , Float64.(extrema(dot.((fsva,), eachrow(sparse_points))))

function really_normal_form(m)
    columns = Dict(var => i for (i, var) in enumerate(all_variables(m)))
    I, J, V = Int[], Int[], Float64[]
    b = Float64[]
    num_slack_vars = 0
    for c in all_constraints(m, AffExpr, MOI.EqualTo{Float64})
        c_obj = constraint_object(c)
        set = MOI.Interval(c_obj.set)
        @assert set.lower == set.upper
        push!(b, set.lower)
        row = (length(I) == 0 ? 0 : I[end-1]) + 1
        for (var, coef) in c_obj.func.terms
            push!(I, row)
            push!(J, columns[var])
            push!(V, coef)
        end
    end
    for c in all_constraints(m, VariableRef, MOI.GreaterThan{Float64})
        set = MOI.Interval(constraint_object(c).set)
        @assert set.lower == 0
        @assert set.upper == Inf
    end
    for c in all_constraints(m, AffExpr, MOI.LessThan{Float64})
        num_slack_vars += 1
        # add slack variables
        c_obj = constraint_object(c)
        set = MOI.Interval(c_obj.set)
        @assert set.lower == -Inf
        push!(b, set.upper)
        row = (length(I) == 0 ? 0 : I[end-1]) + 1
        for (var, coef) in c_obj.func.terms
            push!(I, row)
            push!(J, columns[var])
            push!(V, coef)
        end
        push!(I, row)
        push!(J, length(columns) + num_slack_vars)
        push!(V, 1.0)
    end
    
    A_eff = sparse(I, J, V, I[end-1], length(columns) + num_slack_vars)
    b_eff = b

    return A_eff, b_eff, [repr.(all_variables(m)); ["s($i)" for i in 1:num_slack_vars]]
end


function get_soln_of_perm(i, num_verts)
    perm = lehmer_to_permutation(i, num_verts)

    pos_idxes = Int[]

    for i in 1:num_verts
        push!(pos_idxes, var_idx_tuple_lookup[(perm[i], i)])
    end

    for i in 1:num_verts
        for j in (i+1):num_verts
            for k in (j+1):num_verts
                push!(pos_idxes, var_idx_tuple_lookup[(perm[i], i, perm[j], j, perm[k], k)])
            end
        end
    end

    pos_idxes
end

function compute_verts(num_verts)
    pointI = Int[]
    pointJ = Int[]
    pointV = Int[]
    for i in 1:factorial(num_verts)
        js = get_soln_of_perm(i, num_verts)
        for j in js
            push!(pointI, i)
            push!(pointJ, j)
            push!(pointV, 1.0)
        end
    end
    pointI, pointJ, pointV
end
