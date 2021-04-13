module SparseDecomposable

using LinearAlgebra
using HomotopyContinuation
using SmithNormalForm
using Combinatorics

export HomotopyContinuation
export LinearAlgebra

export solve_generic_simple, solve_binomial
export latticeGens, systemRank, smith_normal_form

export latticeIndex, isLacunary
export minimalSubsystem,triangularReduction

export latticeReduction
export sparse_system
export solveDecomposable
export certify_process
export monomialMapEvaluation

function isLacunary(A)
    latticeIndex(A)>1
end

#outputs the map P which is the monom
# change of coordinates making the
# triangularity obvious
# The original system after the change of coordinates
# and the subsystem after change of coordinates
function triangularReduction(A,C)
    n=length(A)
    I = minimalSubsystem(A)
    L = unique(vcat(I,1:n))
    (D,P,Q,d) = smith_normal_form(latticeGens(A[I]))
    B=[P*(latticeGens(M)) for M in A]
    (P,(B[L],C[L]),([b[1:length(I),:] for b in B[I]],C[I]))
end

function minimalSubsystem(A)
    m=length(A)
    if m>10
        println("minimal subsystem is too dumb")
        return nothing
    end
    for p in powerset(1:m)
        if length(p)>0 && systemRank(A[p])==length(p)
            return Array{Int64,1}(p)
        end
    end
end


function latticeIndex(A)
    M=latticeGens(A)
    last(smith_normal_form(M))
end


##TODO: fix so that you only call smith_normal_form
function latticeReduction(A)
    n = size(A,2)
    F=smith(latticeGens(A))
    phi = F.S*diagm(F.SNF)
    invphi= diagm([1//i for i in F.SNF])*F.Sinv
    reducedSupports=[Array{Int64,2}(invphi*latticeGens(B)) for B in A]
    return (phi,reducedSupports)
end

## Returns (D,P,Q,d) where PAQ = D and D is a "diagonal" rectangular matrix
## with product of entries d
function smith_normal_form(A)
    S = smith(A)
    P = S.Sinv
    Q = S.Tinv
    D = P*A*Q
    d=prod(S.SNF)
    return (D,P,Q,d)
end

function solve_binomial(E,b)
    BSS=HomotopyContinuation.BinomialSystemSolver(E,b)
    HomotopyContinuation.solve!(BSS)
    map(x->Array{ComplexF64,1}(x),collect(eachcol(BSS.X)))
end

#translating a matrix to origin
function latticeGens(A::Array{Int64,2})
    m=size(A,2) # number of cols
    B=copy(A)
    for i in 1:m
        B[:,i]-=A[:,1]
    end
    B
end
#translating a list of supports to origin
function latticeGens(A::Array{Array{Int64,2},1})
    hcat([latticeGens(a) for a in A]...)
end

function systemRank(A::Array{Array{Int64,2},1})
    rank(latticeGens(A))
end

function sparse_system(A,C)
    F=System(A,C;variables=variables(:x,1:length(A)))
end

function solve_generic_simple(A,C)
#=
    C=Array{Array{Float64,1},1}([])
    for a in A
        fi_coeffs=[]
        for m in 1:size(a,2)
            push!(fi_coeffs,rand(Float64))
        end
        push!(C,fi_coeffs)
    end
    println(A)
    println(C)
    println(variables(:x,1:length(A)))
    =#
    F=System(A,C;variables=variables(:x,1:length(A)))
    solutions(solve(F))
end

function solveDecomposable(A,C; LacunarySystem=true,TriangularSystem=true, Name="System 1",Num=1)
    #put in a function which shifts A into positive orthant

    for i in 1:Num
        print("  ")
    end
    print("Starting call on "*Name*"\n")
    C=convert(Array{Array{ComplexF64,1},1},C)
    n=length(A)
    for a in A
        for i in 1:n
            mymin = min(a[i,:]...)
            for j in 1:size(a,2)
                a[i,j]-=mymin
            end
        end
    end

    if LacunarySystem==true
        if latticeIndex(A)>1
            for i in 1:Num
                print("  ")
            end
            print("->lacunary\n")
            (phi,A2) = latticeReduction(A)
            NewNum=1+Num
            NewName="System "*string(NewNum)
            lacBottomFib=solveDecomposable(A2,C;LacunarySystem=false,TriangularSystem=TriangularSystem,Name=NewName,Num=NewNum)
            lacSolns=collect(Iterators.flatten([solve_binomial(phi,z) for z in lacBottomFib]))

            for i in 1:Num
                print("  ")
            end
            print("Finished call on "*Name*" with "*string(length(lacSolns))* " many solutions\n")
            return lacSolns
        else
            for i in 1:Num
                print("  ")
            end
            print("->not lacunary\n")
            return solveDecomposable(A,C;LacunarySystem=false,TriangularSystem=TriangularSystem, Name=Name, Num=Num)
        end
    end
    if TriangularSystem==true
        r = length(minimalSubsystem(A))
        if r<n
            for i in 1:Num
                print("  ")
            end
            print("->triangular\n")
            (P,F,S) = triangularReduction(A,C)
            #B is the supports of the image of A under P
            # after permutation which ensures the first r supports/coeffs form
            # the triangular system.
            # Note also: the variable order is changed so that hte first r variables
            #  are the relevant ones for the triangular system.
            # otherwise, F will have many 0's in the supports,
            # S=(supp,coeff) is the triangular system (first r of F) WITHOUT those zeros
            B = first(F)
            #C is the coefficients
            C1 = last(F)


            NewNum=1+Num
            NewName="System "*string(NewNum)
            triBottomFib = solveDecomposable(S[1],S[2];LacunarySystem=true,TriangularSystem=false,Name=NewName,Num=NewNum)

            allfibres=[]
            counter=0
            for s in triBottomFib
                counter+=1
                newSupport=[b[r+1:n,:] for b in B[r+1:n]]
                oldSupport=B[r+1:n]
                newCoeffs=[]

                for i in r+1:n
                    iCoeff=copy(C1[i])
                    #now we multiply each coefficient
                    for j in 1:length(iCoeff)
                        multiplier = 1
                        for k in 1:r
                            multiplier*=s[k]^B[i][k,j]
                        end
                        iCoeff[j]*=multiplier
                    end
                    push!(newCoeffs,iCoeff)
                end

                newSols=solveDecomposable(newSupport,newCoeffs,Name=Name*" fibre "*string(counter),Num=Num)
                newConcatenatedSols=[vcat(s,n) for n in newSols]
                for newsol in newConcatenatedSols
                    push!(allfibres,newsol)
                end
            end

            correctSols=[monomialMapEvaluation(p,(P)) for p in allfibres]

            for i in 1:Num
                print("  ")
            end
            print("Finished call on "*Name*" with "*string(length(correctSols))* " many solutions\n")
            return correctSols
        else
            for i in 1:Num
                print("  ")
            end
            print("->not triangular\n")
            return solveDecomposable(A,C;LacunarySystem=LacunarySystem,TriangularSystem=false, Name=Name, Num=Num)
        end
    end
    if LacunarySystem==false && TriangularSystem==false
        for i in 1:Num
            print("  ")
        end
        print("->Not lacunary nor triangular\n")
        S=solve_generic_simple(A,C)

        for i in 1:Num
            print("  ")
        end
        print("Finished call on "*Name*" with "*string(length(S))* " many solutions\n")

        return S
    end
end

function monomialMapEvaluation(v,A)

    k=length(v)
    return ([prod([v[i]^(A[i,j]) for i in 1:size(A,1)]) for j in 1:size(A,2)])
end
function certify_process(A,C)
    S=solveDecomposable(A,C)
    F=sparse_system(A,C)
    certify(F,S)
end

greet() = print("Hello World!")

end # module
