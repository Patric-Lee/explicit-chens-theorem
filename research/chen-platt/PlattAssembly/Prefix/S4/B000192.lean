import PlattAssemblyKernel
import PlattCertificates.Count131072.C036144
import PlattCertificates.Count131072.C036145
import PlattCertificates.Count131072.C036146
import PlattCertificates.Count131072.C036147
import PlattCertificates.Count131072.C036148
import PlattCertificates.Count131072.C036149
import PlattCertificates.Count131072.C036150
import PlattCertificates.Count131072.C036151
import PlattCertificates.Count131072.C036152
import PlattCertificates.Count131072.C036153
import PlattCertificates.Count131072.C036154
import PlattCertificates.Count131072.C036155
import PlattCertificates.Count131072.C036156
import PlattCertificates.Count131072.C036157
import PlattCertificates.Count131072.C036158
import PlattCertificates.Count131072.C036159
import PlattCertificates.Count131072.C036160
import PlattCertificates.Count131072.C036161
import PlattCertificates.Count131072.C036162
import PlattCertificates.Count131072.C036163
import PlattCertificates.Count131072.C036164
import PlattCertificates.Count131072.C036165
import PlattCertificates.Count131072.C036166
import PlattCertificates.Count131072.C036167
import PlattCertificates.Count131072.C036168
import PlattCertificates.Count131072.C036169
import PlattCertificates.Count131072.C036170
import PlattCertificates.Count131072.C036171
import PlattCertificates.Count131072.C036172
import PlattCertificates.Count131072.C036173
import PlattCertificates.Count131072.C036174
import PlattCertificates.Count131072.C036175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36144 : List PrefixCut := [⟨64,354228300,354228513⟩]
theorem checked36144 : checkPrefixCuts (2^48) 4741398529 10 Manual.Count131072.C036144.packed 64 cuts36144 = true := by
 decide +kernel
def cuts36145 : List PrefixCut := [⟨9,50874620,50874649⟩,
⟨64,351665906,351666123⟩]
theorem checked36145 : checkPrefixCuts (2^48) 4741529601 10 Manual.Count131072.C036145.packed 64 cuts36145 = true := by
 decide +kernel
def pointBounds36145 : List (Nat × Nat × Nat) := [(4741548032,107589926848502,107590311582837)]
theorem point_links_checked36145 : (cuts36145.take 1).map (fun c => (4741529601-1+2*2^10*c.k,107589875973882+c.lower,107590260708188+c.upper)) = pointBounds36145 := by
 decide +kernel
def cuts36146 : List PrefixCut := [⟨18,96106851,96106913⟩,
⟨64,345541933,345542145⟩]
theorem checked36146 : checkPrefixCuts (2^48) 4741660673 10 Manual.Count131072.C036146.packed 64 cuts36146 = true := by
 decide +kernel
def pointBounds36146 : List (Nat × Nat × Nat) := [(4741697536,107590323746639,107590708481224)]
theorem point_links_checked36146 : (cuts36146.take 1).map (fun c => (4741660673-1+2*2^10*c.k,107590227639788+c.lower,107590612374311+c.upper)) = pointBounds36146 := by
 decide +kernel
def cuts36147 : List PrefixCut := [⟨27,147391135,147391227⟩,
⟨64,346660255,346660467⟩]
theorem checked36147 : checkPrefixCuts (2^48) 4741791745 10 Manual.Count131072.C036147.packed 64 cuts36147 = true := by
 decide +kernel
def pointBounds36147 : List (Nat × Nat × Nat) := [(4741847040,107590720572856,107591105307683)]
theorem point_links_checked36147 : (cuts36147.take 1).map (fun c => (4741791745-1+2*2^10*c.k,107590573181721+c.lower,107590957916456+c.upper)) = pointBounds36147 := by
 decide +kernel
def cuts36148 : List PrefixCut := [⟨36,194101810,194101931⟩,
⟨64,348787522,348787739⟩]
theorem checked36148 : checkPrefixCuts (2^48) 4741922817 10 Manual.Count131072.C036148.packed 64 cuts36148 = true := by
 decide +kernel
def pointBounds36148 : List (Nat × Nat × Nat) := [(4741996544,107591113943786,107591498678854)]
theorem point_links_checked36148 : (cuts36148.take 1).map (fun c => (4741922817-1+2*2^10*c.k,107590919841976+c.lower,107591304576923+c.upper)) = pointBounds36148 := by
 decide +kernel
def cuts36149 : List PrefixCut := [⟨45,246685952,246686104⟩,
⟨64,348065601,348065819⟩]
theorem checked36149 : checkPrefixCuts (2^48) 4742053889 10 Manual.Count131072.C036149.packed 64 cuts36149 = true := by
 decide +kernel
def pointBounds36149 : List (Nat × Nat × Nat) := [(4742146048,107591515315450,107591900050766)]
theorem point_links_checked36149 : (cuts36149.take 1).map (fun c => (4742053889-1+2*2^10*c.k,107591268629498+c.lower,107591653364662+c.upper)) = pointBounds36149 := by
 decide +kernel
def cuts36150 : List PrefixCut := [⟨54,298851604,298851788⟩,
⟨64,353041820,353042038⟩]
theorem checked36150 : checkPrefixCuts (2^48) 4742184961 10 Manual.Count131072.C036150.packed 64 cuts36150 = true := by
 decide +kernel
def pointBounds36150 : List (Nat × Nat × Nat) := [(4742295552,107591915546703,107592300282269)]
theorem point_links_checked36150 : (cuts36150.take 1).map (fun c => (4742184961-1+2*2^10*c.k,107591616695099+c.lower,107592001430481+c.upper)) = pointBounds36150 := by
 decide +kernel
def cuts36151 : List PrefixCut := [⟨63,343001432,343001653⟩,
⟨64,347630908,347631132⟩]
theorem checked36151 : checkPrefixCuts (2^48) 4742316033 10 Manual.Count131072.C036151.packed 64 cuts36151 = true := by
 decide +kernel
def pointBounds36151 : List (Nat × Nat × Nat) := [(4742445056,107592312738351,107592697474172)]
theorem point_links_checked36151 : (cuts36151.take 1).map (fun c => (4742316033-1+2*2^10*c.k,107591969736919+c.lower,107592354472519+c.upper)) = pointBounds36151 := by
 decide +kernel
def cuts36152 : List PrefixCut := [⟨64,352013283,352013503⟩]
theorem checked36152 : checkPrefixCuts (2^48) 4742447105 10 Manual.Count131072.C036152.packed 64 cuts36152 = true := by
 decide +kernel
def cuts36153 : List PrefixCut := [⟨8,42613666,42613692⟩,
⟨64,345653159,345653371⟩]
theorem checked36153 : checkPrefixCuts (2^48) 4742578177 10 Manual.Count131072.C036153.packed 64 cuts36153 = true := by
 decide +kernel
def pointBounds36153 : List (Nat × Nat × Nat) := [(4742594560,107592711994776,107593096730846)]
theorem point_links_checked36153 : (cuts36153.take 1).map (fun c => (4742578177-1+2*2^10*c.k,107592669381110+c.lower,107593054117154+c.upper)) = pointBounds36153 := by
 decide +kernel
def cuts36154 : List PrefixCut := [⟨17,91159676,91159734⟩,
⟨64,344397311,344397525⟩]
theorem checked36154 : checkPrefixCuts (2^48) 4742709249 10 Manual.Count131072.C036154.packed 64 cuts36154 = true := by
 decide +kernel
def pointBounds36154 : List (Nat × Nat × Nat) := [(4742744064,107593106193945,107593490930259)]
theorem point_links_checked36154 : (cuts36154.take 1).map (fun c => (4742709249-1+2*2^10*c.k,107593015034269+c.lower,107593399770525+c.upper)) = pointBounds36154 := by
 decide +kernel
def cuts36155 : List PrefixCut := [⟨26,141661262,141661348⟩,
⟨64,347948574,347948783⟩]
theorem checked36155 : checkPrefixCuts (2^48) 4742840321 10 Manual.Count131072.C036155.packed 64 cuts36155 = true := by
 decide +kernel
def pointBounds36155 : List (Nat × Nat × Nat) := [(4742893568,107593501092842,107593885829398)]
theorem point_links_checked36155 : (cuts36155.take 1).map (fun c => (4742840321-1+2*2^10*c.k,107593359431580+c.lower,107593744168050+c.upper)) = pointBounds36155 := by
 decide +kernel
def cuts36156 : List PrefixCut := [⟨35,193109399,193109517⟩,
⟨64,351262255,351262468⟩]
theorem checked36156 : checkPrefixCuts (2^48) 4742971393 10 Manual.Count131072.C036156.packed 64 cuts36156 = true := by
 decide +kernel
def pointBounds36156 : List (Nat × Nat × Nat) := [(4743043072,107593900489553,107594285226350)]
theorem point_links_checked36156 : (cuts36156.take 1).map (fun c => (4742971393-1+2*2^10*c.k,107593707380154+c.lower,107594092116833+c.upper)) = pointBounds36156 := by
 decide +kernel
def cuts36157 : List PrefixCut := [⟨44,237789315,237789459⟩,
⟨64,350896422,350896635⟩]
theorem checked36157 : checkPrefixCuts (2^48) 4743102465 10 Manual.Count131072.C036157.packed 64 cuts36157 = true := by
 decide +kernel
def pointBounds36157 : List (Nat × Nat × Nat) := [(4743192576,107594296431724,107594681168760)]
theorem point_links_checked36157 : (cuts36157.take 1).map (fun c => (4743102465-1+2*2^10*c.k,107594058642409+c.lower,107594443379301+c.upper)) = pointBounds36157 := by
 decide +kernel
def cuts36158 : List PrefixCut := [⟨53,287985412,287985592⟩,
⟨64,348987868,348988085⟩]
theorem checked36158 : checkPrefixCuts (2^48) 4743233537 10 Manual.Count131072.C036158.packed 64 cuts36158 = true := by
 decide +kernel
def pointBounds36158 : List (Nat × Nat × Nat) := [(4743342080,107594697524243,107595082261528)]
theorem point_links_checked36158 : (cuts36158.take 1).map (fun c => (4743233537-1+2*2^10*c.k,107594409538831+c.lower,107594794275936+c.upper)) = pointBounds36158 := by
 decide +kernel
def cuts36159 : List PrefixCut := [⟨62,341086154,341086362⟩,
⟨64,353132002,353132217⟩]
theorem checked36159 : checkPrefixCuts (2^48) 4743364609 10 Manual.Count131072.C036159.packed 64 cuts36159 = true := by
 decide +kernel
def pointBounds36159 : List (Nat × Nat × Nat) := [(4743491584,107595099612853,107595484350383)]
theorem point_links_checked36159 : (cuts36159.take 1).map (fun c => (4743364609-1+2*2^10*c.k,107594758526699+c.lower,107595143264021+c.upper)) = pointBounds36159 := by
 decide +kernel
def cuts36160 : List PrefixCut := [⟨64,346891746,346891955⟩]
theorem checked36160 : checkPrefixCuts (2^48) 4743495681 10 Manual.Count131072.C036160.packed 64 cuts36160 = true := by
 decide +kernel
def cuts36161 : List PrefixCut := [⟨7,38569308,38569331⟩,
⟨64,352459772,352459983⟩]
theorem checked36161 : checkPrefixCuts (2^48) 4743626753 10 Manual.Count131072.C036161.packed 64 cuts36161 = true := by
 decide +kernel
def pointBounds36161 : List (Nat × Nat × Nat) := [(4743641088,107595497119755,107595881857524)]
theorem point_links_checked36161 : (cuts36161.take 1).map (fun c => (4743626753-1+2*2^10*c.k,107595458550447+c.lower,107595843288193+c.upper)) = pointBounds36161 := by
 decide +kernel
def cuts36162 : List PrefixCut := [⟨16,85858676,85858726⟩,
⟨64,345685885,345686095⟩]
theorem checked36162 : checkPrefixCuts (2^48) 4743757825 10 Manual.Count131072.C036162.packed 64 cuts36162 = true := by
 decide +kernel
def pointBounds36162 : List (Nat × Nat × Nat) := [(4743790592,107595896868895,107596281606902)]
theorem point_links_checked36162 : (cuts36162.take 1).map (fun c => (4743757825-1+2*2^10*c.k,107595811010219+c.lower,107596195748176+c.upper)) = pointBounds36162 := by
 decide +kernel
def cuts36163 : List PrefixCut := [⟨25,137951289,137951375⟩,
⟨64,349354986,349355204⟩]
theorem checked36163 : checkPrefixCuts (2^48) 4743888897 10 Manual.Count131072.C036163.packed 64 cuts36163 = true := by
 decide +kernel
def pointBounds36163 : List (Nat × Nat × Nat) := [(4743940096,107596294647393,107596679385646)]
theorem point_links_checked36163 : (cuts36163.take 1).map (fun c => (4743888897-1+2*2^10*c.k,107596156696104+c.lower,107596541434271+c.upper)) = pointBounds36163 := by
 decide +kernel
def cuts36164 : List PrefixCut := [⟨34,184938259,184938374⟩,
⟨64,346734760,346734973⟩]
theorem checked36164 : checkPrefixCuts (2^48) 4744019969 10 Manual.Count131072.C036164.packed 64 cuts36164 = true := by
 decide +kernel
def pointBounds36164 : List (Nat × Nat × Nat) := [(4744089600,107596690989349,107597075727849)]
theorem point_links_checked36164 : (cuts36164.take 1).map (fun c => (4744019969-1+2*2^10*c.k,107596506051090+c.lower,107596890789475+c.upper)) = pointBounds36164 := by
 decide +kernel
def cuts36165 : List PrefixCut := [⟨43,232278443,232278590⟩,
⟨64,345241919,345242137⟩]
theorem checked36165 : checkPrefixCuts (2^48) 4744151041 10 Manual.Count131072.C036165.packed 64 cuts36165 = true := by
 decide +kernel
def pointBounds36165 : List (Nat × Nat × Nat) := [(4744239104,107597085064293,107597469803038)]
theorem point_links_checked36165 : (cuts36165.take 1).map (fun c => (4744151041-1+2*2^10*c.k,107596852785850+c.lower,107597237524448+c.upper)) = pointBounds36165 := by
 decide +kernel
def cuts36166 : List PrefixCut := [⟨52,281633012,281633190⟩,
⟨64,347308888,347309111⟩]
theorem checked36166 : checkPrefixCuts (2^48) 4744282113 10 Manual.Count131072.C036166.packed 64 cuts36166 = true := by
 decide +kernel
def pointBounds36166 : List (Nat × Nat × Nat) := [(4744388608,107597479660781,107597864399775)]
theorem point_links_checked36166 : (cuts36166.take 1).map (fun c => (4744282113-1+2*2^10*c.k,107597198027769+c.lower,107597582766585+c.upper)) = pointBounds36166 := by
 decide +kernel
def cuts36167 : List PrefixCut := [⟨61,334662844,334663049⟩,
⟨64,350740203,350740418⟩]
theorem checked36167 : checkPrefixCuts (2^48) 4744413185 10 Manual.Count131072.C036167.packed 64 cuts36167 = true := by
 decide +kernel
def pointBounds36167 : List (Nat × Nat × Nat) := [(4744538112,107597879999501,107598264738745)]
theorem point_links_checked36167 : (cuts36167.take 1).map (fun c => (4744413185-1+2*2^10*c.k,107597545336657+c.lower,107597930075696+c.upper)) = pointBounds36167 := by
 decide +kernel
def cuts36168 : List PrefixCut := [⟨64,351679754,351679969⟩]
theorem checked36168 : checkPrefixCuts (2^48) 4744544257 10 Manual.Count131072.C036168.packed 64 cuts36168 = true := by
 decide +kernel
def cuts36169 : List PrefixCut := [⟨6,28890930,28890950⟩,
⟨64,343008706,343008919⟩]
theorem checked36169 : checkPrefixCuts (2^48) 4744675329 10 Manual.Count131072.C036169.packed 64 cuts36169 = true := by
 decide +kernel
def pointBounds36169 : List (Nat × Nat × Nat) := [(4744687616,107598276647544,107598661387033)]
theorem point_links_checked36169 : (cuts36169.take 1).map (fun c => (4744675329-1+2*2^10*c.k,107598247756614+c.lower,107598632496083+c.upper)) = pointBounds36169 := by
 decide +kernel
def cuts36170 : List PrefixCut := [⟨15,83644783,83644835⟩,
⟨64,349939972,349940182⟩]
theorem checked36170 : checkPrefixCuts (2^48) 4744806401 10 Manual.Count131072.C036170.packed 64 cuts36170 = true := by
 decide +kernel
def pointBounds36170 : List (Nat × Nat × Nat) := [(4744837120,107598674410103,107599059149837)]
theorem point_links_checked36170 : (cuts36170.take 1).map (fun c => (4744806401-1+2*2^10*c.k,107598590765320+c.lower,107598975505002+c.upper)) = pointBounds36170 := by
 decide +kernel
def cuts36171 : List PrefixCut := [⟨24,129141357,129141439⟩,
⟨64,351116682,351116902⟩]
theorem checked36171 : checkPrefixCuts (2^48) 4744937473 10 Manual.Count131072.C036171.packed 64 cuts36171 = true := by
 decide +kernel
def pointBounds36171 : List (Nat × Nat × Nat) := [(4744986624,107599069846649,107599454586623)]
theorem point_links_checked36171 : (cuts36171.take 1).map (fun c => (4744937473-1+2*2^10*c.k,107598940705292+c.lower,107599325445184+c.upper)) = pointBounds36171 := by
 decide +kernel
def cuts36172 : List PrefixCut := [⟨33,182939914,182940023⟩,
⟨64,350988412,350988622⟩]
theorem checked36172 : checkPrefixCuts (2^48) 4745068545 10 Manual.Count131072.C036172.packed 64 cuts36172 = true := by
 decide +kernel
def pointBounds36172 : List (Nat × Nat × Nat) := [(4745136128,107599474761888,107599859502109)]
theorem point_links_checked36172 : (cuts36172.take 1).map (fun c => (4745068545-1+2*2^10*c.k,107599291821974+c.lower,107599676562086+c.upper)) = pointBounds36172 := by
 decide +kernel
def cuts36173 : List PrefixCut := [⟨42,229142667,229142809⟩,
⟨64,348961928,348962141⟩]
theorem checked36173 : checkPrefixCuts (2^48) 4745199617 10 Manual.Count131072.C036173.packed 64 cuts36173 = true := by
 decide +kernel
def pointBounds36173 : List (Nat × Nat × Nat) := [(4745285632,107599871953053,107600256693517)]
theorem point_links_checked36173 : (cuts36173.take 1).map (fun c => (4745199617-1+2*2^10*c.k,107599642810386+c.lower,107600027550708+c.upper)) = pointBounds36173 := by
 decide +kernel
def cuts36174 : List PrefixCut := [⟨51,277181466,277181639⟩,
⟨64,347113507,347113724⟩]
theorem checked36174 : checkPrefixCuts (2^48) 4745330689 10 Manual.Count131072.C036174.packed 64 cuts36174 = true := by
 decide +kernel
def pointBounds36174 : List (Nat × Nat × Nat) := [(4745435136,107600268953780,107600653694488)]
theorem point_links_checked36174 : (cuts36174.take 1).map (fun c => (4745330689-1+2*2^10*c.k,107599991772314+c.lower,107600376512849+c.upper)) = pointBounds36174 := by
 decide +kernel
def cuts36175 : List PrefixCut := [⟨60,330911538,330911747⟩,
⟨64,352382828,352383050⟩]
theorem checked36175 : checkPrefixCuts (2^48) 4745461761 10 Manual.Count131072.C036175.packed 64 cuts36175 = true := by
 decide +kernel
def pointBounds36175 : List (Nat × Nat × Nat) := [(4745584640,107600669797359,107601054538320)]
theorem point_links_checked36175 : (cuts36175.take 1).map (fun c => (4745461761-1+2*2^10*c.k,107600338885821+c.lower,107600723626573+c.upper)) = pointBounds36175 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000192
