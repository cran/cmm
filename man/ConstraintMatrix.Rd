\name{ConstraintMatrix}
\alias{ConstraintMatrix}
\title{ConstraintMatrix}

\description{
 Returns hierarchical model constraint matrix, i.e., nullspace of design matrix
}

\usage{
ConstraintMatrix(var, suffconfigs, dim, SubsetCoding = "Automatic")
}

\arguments{
  \item{var}{character or numeric vector containing variables}
  \item{suffconfigs}{subvector or list of subvectors of \code{var} indicating the sufficient configurations or highest order interactions in model}
  \item{dim}{numeric vector indicating the dimension of \code{var} (must be same length as \code{var})}
  \item{SubsetCoding}{allows a (character) type or a matrix to be assigned to variables for each element of \code{suffconfigs}}, see examples
}

\details{
The model \eqn{\mu_{ij}=\alpha+\beta_{i}+\gamma_j}{mu_ij = alpha + beta_i + gamma_j}
has parametric form and can equivalently be described using constraints on the \eqn{\mu_{ij}}{mu_ij},
by \eqn{\mu_{ij}-\mu_{il}-\mu_{kj}+\mu_{kl}=0}{mu_ij - mu_il - mu_kj + mu_kl = 0}.
Returns the transpose of the null space of \code{DesignMatrix(var,marg,dim)}. Rows normally sum to zero.
See \code{\link{DesignMatrix}} for more details.
}

\value{
 matrix
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer.
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk}
}

\seealso{
 \code{\link{ConstraintMatrix}}, \code{\link{DesignMatrix}}, \code{\link{DirectSum}}, \code{\link{MarginalMatrix}}
}

\examples{

# Constraint matrix for independence model
var <- c("A","B")
suffconfigs <- list(c("A"),c("B"))
dim <- c(3, 3)
ConstraintMatrix(var,suffconfigs,dim)
# notation in one line
ConstraintMatrix(c("A","B"),list(c("A"),c("B")),c(3,3))


# Constraint matrix for saturated model, two short specifications giving same result
ConstraintMatrix(c("A","B"),c("A","B"),c(3,3))
ConstraintMatrix(c("A","B"),list(c("A","B")),c(3,3))


# Constraint matrix for univariate quadratic regression model
var <- c("A")
suffconfigs <- c("A")
dim <- c(5)
ConstraintMatrix(var,suffconfigs,dim,SubsetCoding=list(c("A"),"Quadratic"))
# notation in one line
ConstraintMatrix(c("A"),c("A"),c(5),SubsetCoding=list(c("A"),"Quadratic"))


# Constraint matrix for linear by nominal model, various methods:
# simplest method which assumes equidistant centered scores:
ConstraintMatrix(c("A","B"),c("A","B"),c(3,3),SubsetCoding=list(c("A","B"),list("Linear","Nominal")))
# alternative specification with same result as above:
ConstraintMatrix(c("A","B"),c("A","B"),c(3,3),SubsetCoding=list(c("A","B"),list(rbind(c(-1,0,1)),rbind(c(1,0,0),c(0,1,0)))))
# specifying your own category scores
scores=c(1,2,5);
ConstraintMatrix(c("A","B"),c("A","B"),c(3,3),SubsetCoding=list(c("A","B"),list(rbind(scores),"Nominal")))


# Constraint matrix for nominal by nominal model, equating parameters of last two categories of second variable:
ConstraintMatrix(c("A","B"),c("A","B"),c(3,3),SubsetCoding=list(c("A","B"),list("Nominal",rbind(c(1,0,0),c(0,1,1)))))
}

\keyword{univar}
