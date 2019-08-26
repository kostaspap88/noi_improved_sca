
clear all;
close all;


no_bits = 1;
sigma = 0.1;
no_traces = 400;



range = 2^no_bits-1;

K=0:range;
A=0:range;
B=0:range;
cardK = length(K);
cardA = length(A);
cardB = length(B);
pr_uni = 1/cardA;


% PART1: Compute the theoretical distributions

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



% PART2: Computing the estimated distribution from the device

% simulate the leakage using HW plus noise model
% we assume that we know the POIs involved in the leakage La, Lb

a = randi(range+1,no_traces,1)-1;
k = 0;
b = bitxor(a, k);
la = hw(a) + normrnd(0,sigma,no_traces,1);
lb = hw(b) + normrnd(0,sigma,no_traces,1);

% sort the leakages and deploy the clustering-like technique to compute the
% estimated distribution
[sla, ia] = sort(la);
[slb, ib] = sort(lb);

max_hw = hw(range);
start = 1;
for k=0:max_hw
    finish = start + no_traces * nchoosek(max_hw, k) / 2^no_bits - 1;
    la(ia(start:finish))=k;
    lb(ib(start:finish))=k;
    start = finish + 1;
end
   

Dev_Distribution = zeros(cardA, cardB);
for i=1:no_traces
    Dev_Distribution(la(i)+1, lb(i)+1) = Dev_Distribution(la(i)+1, lb(i)+1) + 1/no_traces;
end


% PART3: Compare the estimated distribution to the hypothetical
% distributions (attack part)

% Here we assume that we have located the correct POIs. If not we need to
% repeat the attack with the Dev_Distribution of other POIs.

for k=K
   [dip(k+1) dhm(k+1) dkai(k+1) dkl(k+1)] = distance(Dev_Distribution, Hyp_Distribution(:,:,k+1), A, B);
end

[v1, i1] = sort(dip);
[v2, i2] = sort(dhm);
[v3, i3] = sort(dkai);
[v4, i4] = sort(dkl);

% print top key candidate for every distance
[i1(1) i2(1) i3(1) i4(1)] - 1


