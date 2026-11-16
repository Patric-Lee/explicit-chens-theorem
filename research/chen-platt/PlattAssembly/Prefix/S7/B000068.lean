import PlattAssemblyKernel
import PlattCertificates.Count131072.C062176
import PlattCertificates.Count131072.C062177
import PlattCertificates.Count131072.C062178
import PlattCertificates.Count131072.C062179
import PlattCertificates.Count131072.C062180
import PlattCertificates.Count131072.C062181
import PlattCertificates.Count131072.C062182
import PlattCertificates.Count131072.C062183
import PlattCertificates.Count131072.C062184
import PlattCertificates.Count131072.C062185
import PlattCertificates.Count131072.C062186
import PlattCertificates.Count131072.C062187
import PlattCertificates.Count131072.C062188
import PlattCertificates.Count131072.C062189
import PlattCertificates.Count131072.C062190
import PlattCertificates.Count131072.C062191
import PlattCertificates.Count131072.C062192
import PlattCertificates.Count131072.C062193
import PlattCertificates.Count131072.C062194
import PlattCertificates.Count131072.C062195
import PlattCertificates.Count131072.C062196
import PlattCertificates.Count131072.C062197
import PlattCertificates.Count131072.C062198
import PlattCertificates.Count131072.C062199
import PlattCertificates.Count131072.C062200
import PlattCertificates.Count131072.C062201
import PlattCertificates.Count131072.C062202
import PlattCertificates.Count131072.C062203
import PlattCertificates.Count131072.C062204
import PlattCertificates.Count131072.C062205
import PlattCertificates.Count131072.C062206
import PlattCertificates.Count131072.C062207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62176 : List PrefixCut := [⟨64,196256672,196256790⟩]
theorem checked62176 : checkPrefixCuts (2^48) 8153464833 10 Manual.Count131072.C062176.packed 64 cuts62176 = true := by
 decide +kernel
def cuts62177 : List PrefixCut := [⟨42,128937365,128937444⟩,
⟨64,198014100,198014218⟩]
theorem checked62177 : checkPrefixCuts (2^48) 8153595905 10 Manual.Count131072.C062177.packed 64 cuts62177 = true := by
 decide +kernel
def pointBounds62177 : List (Nat × Nat × Nat) := [(8153681920,114356653215741,114357041874827)]
theorem point_links_checked62177 : (cuts62177.take 1).map (fun c => (8153595905-1+2*2^10*c.k,114356524278376+c.lower,114356912937383+c.upper)) = pointBounds62177 := by
 decide +kernel
def cuts62178 : List PrefixCut := [⟨64,198563258,198563367⟩]
theorem checked62178 : checkPrefixCuts (2^48) 8153726977 10 Manual.Count131072.C062178.packed 64 cuts62178 = true := by
 decide +kernel
def cuts62179 : List PrefixCut := [⟨39,121304281,121304350⟩,
⟨64,199457581,199457693⟩]
theorem checked62179 : checkPrefixCuts (2^48) 8153858049 10 Manual.Count131072.C062179.packed 64 cuts62179 = true := by
 decide +kernel
def pointBounds62179 : List (Nat × Nat × Nat) := [(8153937920,114357042160015,114357430819318)]
theorem point_links_checked62179 : (cuts62179.take 1).map (fun c => (8153858049-1+2*2^10*c.k,114356920855734+c.lower,114357309514968+c.upper)) = pointBounds62179 := by
 decide +kernel
def cuts62180 : List PrefixCut := [⟨64,195415596,195415707⟩]
theorem checked62180 : checkPrefixCuts (2^48) 8153989121 10 Manual.Count131072.C062180.packed 64 cuts62180 = true := by
 decide +kernel
def cuts62181 : List PrefixCut := [⟨36,110495924,110495988⟩,
⟨64,197103878,197103994⟩]
theorem checked62181 : checkPrefixCuts (2^48) 8154120193 10 Manual.Count131072.C062181.packed 64 cuts62181 = true := by
 decide +kernel
def pointBounds62181 : List (Nat × Nat × Nat) := [(8154193920,114357426224835,114357814884356)]
theorem point_links_checked62181 : (cuts62181.take 1).map (fun c => (8154120193-1+2*2^10*c.k,114357315728911+c.lower,114357704388368+c.upper)) = pointBounds62181 := by
 decide +kernel
def cuts62182 : List PrefixCut := [⟨64,198343382,198343496⟩]
theorem checked62182 : checkPrefixCuts (2^48) 8154251265 10 Manual.Count131072.C062182.packed 64 cuts62182 = true := by
 decide +kernel
def cuts62183 : List PrefixCut := [⟨33,102553254,102553312⟩,
⟨64,198064047,198064160⟩]
theorem checked62183 : checkPrefixCuts (2^48) 8154382337 10 Manual.Count131072.C062183.packed 64 cuts62183 = true := by
 decide +kernel
def pointBounds62183 : List (Nat × Nat × Nat) := [(8154449920,114357813729425,114358202389170)]
theorem point_links_checked62183 : (cuts62183.take 1).map (fun c => (8154382337-1+2*2^10*c.k,114357711176171+c.lower,114358099835858+c.upper)) = pointBounds62183 := by
 decide +kernel
def cuts62184 : List PrefixCut := [⟨64,199510595,199510711⟩]
theorem checked62184 : checkPrefixCuts (2^48) 8154513409 10 Manual.Count131072.C062184.packed 64 cuts62184 = true := by
 decide +kernel
def cuts62185 : List PrefixCut := [⟨30,91711659,91711707⟩,
⟨64,198299290,198299396⟩]
theorem checked62185 : checkPrefixCuts (2^48) 8154644481 10 Manual.Count131072.C062185.packed 64 cuts62185 = true := by
 decide +kernel
def pointBounds62185 : List (Nat × Nat × Nat) := [(8154705920,114358200462472,114358589122436)]
theorem point_links_checked62185 : (cuts62185.take 1).map (fun c => (8154644481-1+2*2^10*c.k,114358108750813+c.lower,114358497410729+c.upper)) = pointBounds62185 := by
 decide +kernel
def cuts62186 : List PrefixCut := [⟨64,195327708,195327824⟩]
theorem checked62186 : checkPrefixCuts (2^48) 8154775553 10 Manual.Count131072.C062186.packed 64 cuts62186 = true := by
 decide +kernel
def cuts62187 : List PrefixCut := [⟨27,83424927,83424976⟩,
⟨64,197913247,197913359⟩]
theorem checked62187 : checkPrefixCuts (2^48) 8154906625 10 Manual.Count131072.C062187.packed 64 cuts62187 = true := by
 decide +kernel
def pointBounds62187 : List (Nat × Nat × Nat) := [(8154961920,114358585802738,114358974462925)]
theorem point_links_checked62187 : (cuts62187.take 1).map (fun c => (8154906625-1+2*2^10*c.k,114358502377811+c.lower,114358891037949+c.upper)) = pointBounds62187 := by
 decide +kernel
def cuts62188 : List PrefixCut := [⟨64,197219760,197219874⟩]
theorem checked62188 : checkPrefixCuts (2^48) 8155037697 10 Manual.Count131072.C062188.packed 64 cuts62188 = true := by
 decide +kernel
def cuts62189 : List PrefixCut := [⟨24,74517463,74517505⟩,
⟨64,199494559,199494675⟩]
theorem checked62189 : checkPrefixCuts (2^48) 8155168769 10 Manual.Count131072.C062189.packed 64 cuts62189 = true := by
 decide +kernel
def pointBounds62189 : List (Nat × Nat × Nat) := [(8155217920,114358972028281,114359360688687)]
theorem point_links_checked62189 : (cuts62189.take 1).map (fun c => (8155168769-1+2*2^10*c.k,114358897510818+c.lower,114359286171182+c.upper)) = pointBounds62189 := by
 decide +kernel
def cuts62190 : List PrefixCut := [⟨64,198939138,198939250⟩]
theorem checked62190 : checkPrefixCuts (2^48) 8155299841 10 Manual.Count131072.C062190.packed 64 cuts62190 = true := by
 decide +kernel
def cuts62191 : List PrefixCut := [⟨21,66576943,66576982⟩,
⟨64,201351887,201352005⟩]
theorem checked62191 : checkPrefixCuts (2^48) 8155430913 10 Manual.Count131072.C062191.packed 64 cuts62191 = true := by
 decide +kernel
def pointBounds62191 : List (Nat × Nat × Nat) := [(8155473920,114359362521458,114359751182089)]
theorem point_links_checked62191 : (cuts62191.take 1).map (fun c => (8155430913-1+2*2^10*c.k,114359295944515+c.lower,114359684605107+c.upper)) = pointBounds62191 := by
 decide +kernel
def cuts62192 : List PrefixCut := [⟨64,196033654,196033767⟩]
theorem checked62192 : checkPrefixCuts (2^48) 8155561985 10 Manual.Count131072.C062192.packed 64 cuts62192 = true := by
 decide +kernel
def cuts62193 : List PrefixCut := [⟨18,55634330,55634358⟩,
⟨64,196513669,196513780⟩]
theorem checked62193 : checkPrefixCuts (2^48) 8155693057 10 Manual.Count131072.C062193.packed 64 cuts62193 = true := by
 decide +kernel
def pointBounds62193 : List (Nat × Nat × Nat) := [(8155729920,114359748964386,114360137625237)]
theorem point_links_checked62193 : (cuts62193.take 1).map (fun c => (8155693057-1+2*2^10*c.k,114359693330056+c.lower,114360081990879+c.upper)) = pointBounds62193 := by
 decide +kernel
def cuts62194 : List PrefixCut := [⟨64,200720958,200721071⟩]
theorem checked62194 : checkPrefixCuts (2^48) 8155824129 10 Manual.Count131072.C062194.packed 64 cuts62194 = true := by
 decide +kernel
def cuts62195 : List PrefixCut := [⟨15,45003013,45003041⟩,
⟨64,197853297,197853410⟩]
theorem checked62195 : checkPrefixCuts (2^48) 8155955201 10 Manual.Count131072.C062195.packed 64 cuts62195 = true := by
 decide +kernel
def pointBounds62195 : List (Nat × Nat × Nat) := [(8155985920,114360135567696,114360524228771)]
theorem point_links_checked62195 : (cuts62195.take 1).map (fun c => (8155955201-1+2*2^10*c.k,114360090564683+c.lower,114360479225730+c.upper)) = pointBounds62195 := by
 decide +kernel
def cuts62196 : List PrefixCut := [⟨64,196883832,196883942⟩]
theorem checked62196 : checkPrefixCuts (2^48) 8156086273 10 Manual.Count131072.C062196.packed 64 cuts62196 = true := by
 decide +kernel
def cuts62197 : List PrefixCut := [⟨12,37305763,37305784⟩,
⟨64,197605364,197605478⟩]
theorem checked62197 : checkPrefixCuts (2^48) 8156217345 10 Manual.Count131072.C062197.packed 64 cuts62197 = true := by
 decide +kernel
def pointBounds62197 : List (Nat × Nat × Nat) := [(8156241920,114360522607575,114360911268866)]
theorem point_links_checked62197 : (cuts62197.take 1).map (fun c => (8156217345-1+2*2^10*c.k,114360485301812+c.lower,114360873963082+c.upper)) = pointBounds62197 := by
 decide +kernel
def cuts62198 : List PrefixCut := [⟨64,199672772,199672885⟩]
theorem checked62198 : checkPrefixCuts (2^48) 8156348417 10 Manual.Count131072.C062198.packed 64 cuts62198 = true := by
 decide +kernel
def cuts62199 : List PrefixCut := [⟨9,29263906,29263921⟩,
⟨64,198565282,198565395⟩]
theorem checked62199 : checkPrefixCuts (2^48) 8156479489 10 Manual.Count131072.C062199.packed 64 cuts62199 = true := by
 decide +kernel
def pointBounds62199 : List (Nat × Nat × Nat) := [(8156497920,114360911843854,114361300505366)]
theorem point_links_checked62199 : (cuts62199.take 1).map (fun c => (8156479489-1+2*2^10*c.k,114360882579948+c.lower,114361271241445+c.upper)) = pointBounds62199 := by
 decide +kernel
def cuts62200 : List PrefixCut := [⟨64,200805142,200805254⟩]
theorem checked62200 : checkPrefixCuts (2^48) 8156610561 10 Manual.Count131072.C062200.packed 64 cuts62200 = true := by
 decide +kernel
def cuts62201 : List PrefixCut := [⟨6,18806983,18806993⟩,
⟨64,197385610,197385716⟩]
theorem checked62201 : checkPrefixCuts (2^48) 8156741633 10 Manual.Count131072.C062201.packed 64 cuts62201 = true := by
 decide +kernel
def pointBounds62201 : List (Nat × Nat × Nat) := [(8156753920,114361300757355,114361689419087)]
theorem point_links_checked62201 : (cuts62201.take 1).map (fun c => (8156741633-1+2*2^10*c.k,114361281950372+c.lower,114361670612094+c.upper)) = pointBounds62201 := by
 decide +kernel
def cuts62202 : List PrefixCut := [⟨64,197313425,197313535⟩]
theorem checked62202 : checkPrefixCuts (2^48) 8156872705 10 Manual.Count131072.C062202.packed 64 cuts62202 = true := by
 decide +kernel
def cuts62203 : List PrefixCut := [⟨3,8695798,8695801⟩,
⟨64,197758829,197758938⟩]
theorem checked62203 : checkPrefixCuts (2^48) 8157003777 10 Manual.Count131072.C062203.packed 64 cuts62203 = true := by
 decide +kernel
def pointBounds62203 : List (Nat × Nat × Nat) := [(8157009920,114361685345205,114362074007146)]
theorem point_links_checked62203 : (cuts62203.take 1).map (fun c => (8157003777-1+2*2^10*c.k,114361676649407+c.lower,114362065311345+c.upper)) = pointBounds62203 := by
 decide +kernel
def cuts62204 : List PrefixCut := [⟨64,192683241,192683358⟩]
theorem checked62204 : checkPrefixCuts (2^48) 8157134849 10 Manual.Count131072.C062204.packed 64 cuts62204 = true := by
 decide +kernel
def pointBounds62204 : List (Nat × Nat × Nat) := [(8157265920,114362067091477,114362455753641)]
theorem point_links_checked62204 : (cuts62204.take 1).map (fun c => (8157134849-1+2*2^10*c.k,114361874408236+c.lower,114362263070283+c.upper)) = pointBounds62204 := by
 decide +kernel
def cuts62205 : List PrefixCut := [⟨64,195613141,195613248⟩]
theorem checked62205 : checkPrefixCuts (2^48) 8157265921 10 Manual.Count131072.C062205.packed 64 cuts62205 = true := by
 decide +kernel
def cuts62206 : List PrefixCut := [⟨61,188743531,188743636⟩,
⟨64,197783825,197783935⟩]
theorem checked62206 : checkPrefixCuts (2^48) 8157396993 10 Manual.Count131072.C062206.packed 64 cuts62206 = true := by
 decide +kernel
def pointBounds62206 : List (Nat × Nat × Nat) := [(8157521920,114362451448149,114362840110525)]
theorem point_links_checked62206 : (cuts62206.take 1).map (fun c => (8157396993-1+2*2^10*c.k,114362262704618+c.lower,114362651366889+c.upper)) = pointBounds62206 := by
 decide +kernel
def cuts62207 : List PrefixCut := [⟨64,197539093,197539209⟩]
theorem checked62207 : checkPrefixCuts (2^48) 8157528065 10 Manual.Count131072.C062207.packed 64 cuts62207 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000068
