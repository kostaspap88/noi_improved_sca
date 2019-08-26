% compute the distance between 2 probability mass functions

function [dip, dhm, dkai, dkl] = distance(dreal, dhyp, A, B)


dip = 0;
dhm = 0;
dkai = 0;
dkl = 0;

for i=A+1
    for j=B+1
        
        % inner product distance
        dip = dip + dhyp(i,j) * dreal(i,j);
        
        % harmonic mean based distance
        dhm = dhm + (dhyp(i,j) * dreal(i,j))/(dhyp(i,j) + dreal(i,j));
        
        % kai square pearson distance
        dkai = dkai + (dhyp(i,j) - dreal(i,j))^2 / dhyp(i,j);
        
        % kullback leiber distance
        dkl = dkl + dhyp(i,j) * log(dhyp(i,j)/dreal(i,j));
        
        % note that we do not handle specific cases for zero distances
        
    end
end

dip = 1 - dip;
dhm = 1 - 2*dhm;

end