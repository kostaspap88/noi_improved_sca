% author: Kostas Papagiannopoulos -- kostaspap88@gmail.com -- kpcrypto.net
% Based on "Improved Blind Side-Channel Analysis" by Clavier & Reynaud 


clear all;
close all;


no_bits = 1;
sigma = 0.1;
no_traces = 5000;



range = 2^no_bits-1;

K=0:range;
A=0:range;
B=0:range;
C=0:range; % C used in case of 1o masking
cardK = length(K);
cardA = length(A);
cardB = length(B);
cardC = length(C);
pr_uni = 1/cardA;

% PART1: JOINT DISTRIBUTION ATTACK ON UNPROTECTED WITH ML DISTINGUISHER

% PART1A: Compute the theoretical distributions

Hyp_Distribution = zeros(cardA, cardB, cardK);
for k=K
    for a=A
        % compute the discrete part of the leakage function 
        phi_a = hw(a);
        phi_gak = hw(bitxor(a, k));
        
        % compute the joint distribution for every k
        Hyp_Distribution(phi_a+1, phi_gak+1, k+1) = Hyp_Distribution(phi_a+1, phi_gak+1, k+1) + pr_uni;
    end
end

% PART1B: ML computation

% simulate the leakage using HW plus noise model
% we assume that we know the POIs involved in the leakage

m = randi(range+1,no_traces,1)-1;
k = 1;
y = bitxor(m, k);

% here linking the leakage to the hamming weight is straightforward
hm_easy = hw(m) + normrnd(0,sigma,no_traces,1);
hy_easy = hw(y) + normrnd(0,sigma,no_traces,1);

%-------------------------------------------------------------------------
% lets also consider the case of linking L to HW(V) using the variance
% method proposed

% assumed leakage model: l = alpha*HW(v) + beta + N(0,sigma)
% true alpha, beta
alpha = 2.2;
beta = 3.3; 
% simulate data-variant pois based on the newly assumed model
lm =  alpha*hw(m) + beta + normrnd(0,sigma,no_traces,1);
ly =  alpha*hw(y) + beta + normrnd(0,sigma,no_traces,1);
% simulate a data-invariant poi based on the new model. 
% note that there is no data dependence now
l_quiet =  beta + normrnd(0,sigma,no_traces,1);

mean_hw_v = no_bits/2;
var_hw_v = no_bits * 1/4;
alpha_est = sqrt((var(lm)-var(l_quiet))/var_hw_v); 
% we could also have used any other "l_loud" poi

beta_est = mean(lm) - mean_hw_v*alpha_est;

% now convert lm and ly to Hamming weights
hm = (lm - beta_est)/alpha_est;
hy = (ly - beta_est)/alpha_est;

%-------------------------------------------------------------------------


% estimation of sigma 
sigma_m = std(hm);
sigma_y = std(hy);


% technique 1 to compute ML distinguisher
% numerical problems exist
product = ones(cardK,1);
for k=K

for i=1:4 % the product reaches Inf for large number of traces
    
    summation = 0;
    for hm_star = A
        for hy_star = B
            term1 = 1/sigma_m*sqrt(2*pi) * exp(-0.5 * ((hm(i) - hm_star)/sigma_m)^2 ) * 1/sigma_y*sqrt(2*pi) * exp(-0.5 * ((hy(i) - hy_star)/sigma_y)^2 );
            term2 = Hyp_Distribution(hm_star+1,hy_star+1,k+1);
            full_term = term1 * term2;
            summation = summation + full_term;
        end
    end
    
    product(k+1) = product(k+1) * summation;
    
end

end


% technique 2 to compute ML distinguisher

score = zeros(cardK,1);
for k=K

for i=1:no_traces
    
    summation = 0;
    for hm_star = A
        for hy_star = B
            term1 = 1/sigma_m*sqrt(2*pi) * exp(-0.5 * ((hm(i) - hm_star)/sigma_m)^2 ) * 1/sigma_y*sqrt(2*pi) * exp(-0.5 * ((hy(i) - hy_star)/sigma_y)^2 );
            term2 = Hyp_Distribution(hm_star+1,hy_star+1,k+1);
            full_term = term1 * term2;
            summation = summation + full_term;
        end
    end
    
    score(k+1) = score(k+1) + summation;
    
end

end

score

%--------------------------------------------------------------------------

% PART 2: JOINT DISTRIBUTION ATTACK ON 1ST-ORDER BOOLEAN MASKING WITH SAME 
% MASK IN INTERMEDIATES


% PART2A: Compute the theoretical distributions


Hyp_Distribution_1o = zeros(cardA, cardB, cardK);
for k=K % for all key candidates
    for a=A % for all m values
        for c=C % for all m0 values
            % compute the discrete part of the leakage function 
            m1 = bitxor(a,c);
            phi_m1 = hw(m1);
            phi_x1 = hw(bitxor(m1, k));
            % x0 is equal to m0 (same mask in intermediates)
        
            % compute the joint distribution for every k
            Hyp_Distribution_1o(phi_m1+1, phi_x1+1, k+1) = Hyp_Distribution_1o(phi_m1+1, phi_x1+1, k+1) + pr_uni^2;
        end
    end
end

% simulate the leakage using HW plus noise model for the 1st-order boolean
% case, where the same mask is used in consecutive values
% we assume that we know the POIs involved in the leakage

m = randi(range+1,no_traces,1)-1;
m0 = randi(range+1,no_traces,1)-1;
m1 = bitxor(m,m0);
% we now have shares (m0,m1)

k = 0;
x1 = bitxor(m1, k);
x0 = m0;
x = bitxor(m,k);
% we now have shares (x0,x1) = (m0,m1 XOR k)
% i.e. both value m and value x have been masked with the same mask m0

% here linking the leakage to the hamming weight is straightforward
hm1 = hw(m1) + normrnd(0,sigma,no_traces,1);
hx1 = hw(x1) + normrnd(0,sigma,no_traces,1);



% estimation of sigma 
sigma_m1 = std(hm1);
sigma_x1 = std(hx1);

score_1o = zeros(cardK,1);
for k=K

for i=1:no_traces
    
    summation = 0;
    for hm1_star = A
        for hx1_star = B
            term1 = 1/sigma_m1*sqrt(2*pi) * exp(-0.5 * ((hm1(i) - hm1_star)/sigma_m1)^2 ) * 1/sigma_x1*sqrt(2*pi) * exp(-0.5 * ((hx1(i) - hx1_star)/sigma_x1)^2 );
            term2 = Hyp_Distribution_1o(hm1_star+1,hx1_star+1,k+1);
            full_term = term1 * term2;
            summation = summation + full_term;
        end
    end
    
    score_1o(k+1) = score_1o(k+1) + summation;
    
end

end

score_1o
