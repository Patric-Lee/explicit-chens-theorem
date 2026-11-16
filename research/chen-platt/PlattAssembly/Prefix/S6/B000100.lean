import PlattAssemblyKernel
import PlattCertificates.Count131072.C053200
import PlattCertificates.Count131072.C053201
import PlattCertificates.Count131072.C053202
import PlattCertificates.Count131072.C053203
import PlattCertificates.Count131072.C053204
import PlattCertificates.Count131072.C053205
import PlattCertificates.Count131072.C053206
import PlattCertificates.Count131072.C053207
import PlattCertificates.Count131072.C053208
import PlattCertificates.Count131072.C053209
import PlattCertificates.Count131072.C053210
import PlattCertificates.Count131072.C053211
import PlattCertificates.Count131072.C053212
import PlattCertificates.Count131072.C053213
import PlattCertificates.Count131072.C053214
import PlattCertificates.Count131072.C053215
import PlattCertificates.Count131072.C053216
import PlattCertificates.Count131072.C053217
import PlattCertificates.Count131072.C053218
import PlattCertificates.Count131072.C053219
import PlattCertificates.Count131072.C053220
import PlattCertificates.Count131072.C053221
import PlattCertificates.Count131072.C053222
import PlattCertificates.Count131072.C053223
import PlattCertificates.Count131072.C053224
import PlattCertificates.Count131072.C053225
import PlattCertificates.Count131072.C053226
import PlattCertificates.Count131072.C053227
import PlattCertificates.Count131072.C053228
import PlattCertificates.Count131072.C053229
import PlattCertificates.Count131072.C053230
import PlattCertificates.Count131072.C053231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53200 : List PrefixCut := [⟨64,230722160,230722291⟩]
theorem checked53200 : checkPrefixCuts (2^48) 6976962561 10 Manual.Count131072.C053200.packed 64 cuts53200 = true := by
 decide +kernel
def cuts53201 : List PrefixCut := [⟨38,141481113,141481194⟩,
⟨64,236890211,236890344⟩]
theorem checked53201 : checkPrefixCuts (2^48) 6977093633 10 Manual.Count131072.C053201.packed 64 cuts53201 = true := by
 decide +kernel
def pointBounds53201 : List (Nat × Nat × Nat) := [(6977171456,112428187323062,112428574883552)]
theorem point_links_checked53201 : (cuts53201.take 1).map (fun c => (6977093633-1+2*2^10*c.k,112428045841949+c.lower,112428433402358+c.upper)) = pointBounds53201 := by
 decide +kernel
def cuts53202 : List PrefixCut := [⟨64,230673141,230673271⟩]
theorem checked53202 : checkPrefixCuts (2^48) 6977224705 10 Manual.Count131072.C053202.packed 64 cuts53202 = true := by
 decide +kernel
def cuts53203 : List PrefixCut := [⟨17,62286652,62286686⟩,
⟨64,231515961,231516093⟩]
theorem checked53203 : checkPrefixCuts (2^48) 6977355777 10 Manual.Count131072.C053203.packed 64 cuts53203 = true := by
 decide +kernel
def pointBounds53203 : List (Nat × Nat × Nat) := [(6977390592,112428575691953,112428963252659)]
theorem point_links_checked53203 : (cuts53203.take 1).map (fun c => (6977355777-1+2*2^10*c.k,112428513405301+c.lower,112428900965973+c.upper)) = pointBounds53203 := by
 decide +kernel
def cuts53204 : List PrefixCut := [⟨60,218965994,218966118⟩,
⟨64,234295082,234295215⟩]
theorem checked53204 : checkPrefixCuts (2^48) 6977486849 10 Manual.Count131072.C053204.packed 64 cuts53204 = true := by
 decide +kernel
def pointBounds53204 : List (Nat × Nat × Nat) := [(6977609728,112428963887256,112429351448184)]
theorem point_links_checked53204 : (cuts53204.take 1).map (fun c => (6977486849-1+2*2^10*c.k,112428744921262+c.lower,112429132482066+c.upper)) = pointBounds53204 := by
 decide +kernel
def cuts53205 : List PrefixCut := [⟨64,233604887,233605025⟩]
theorem checked53205 : checkPrefixCuts (2^48) 6977617921 10 Manual.Count131072.C053205.packed 64 cuts53205 = true := by
 decide +kernel
def cuts53206 : List PrefixCut := [⟨39,143605743,143605825⟩,
⟨64,233963573,233963706⟩]
theorem checked53206 : checkPrefixCuts (2^48) 6977748993 10 Manual.Count131072.C053206.packed 64 cuts53206 = true := by
 decide +kernel
def pointBounds53206 : List (Nat × Nat × Nat) := [(6977828864,112429356426974,112429743988131)]
theorem point_links_checked53206 : (cuts53206.take 1).map (fun c => (6977748993-1+2*2^10*c.k,112429212821231+c.lower,112429600382306+c.upper)) = pointBounds53206 := by
 decide +kernel
def cuts53207 : List PrefixCut := [⟨64,236419767,236419898⟩]
theorem checked53207 : checkPrefixCuts (2^48) 6977880065 10 Manual.Count131072.C053207.packed 64 cuts53207 = true := by
 decide +kernel
def cuts53208 : List PrefixCut := [⟨18,66354862,66354902⟩,
⟨64,232139642,232139775⟩]
theorem checked53208 : checkPrefixCuts (2^48) 6978011137 10 Manual.Count131072.C053208.packed 64 cuts53208 = true := by
 decide +kernel
def pointBounds53208 : List (Nat × Nat × Nat) := [(6978048000,112429749559433,112430137120812)]
theorem point_links_checked53208 : (cuts53208.take 1).map (fun c => (6978011137-1+2*2^10*c.k,112429683204571+c.lower,112430070765910+c.upper)) = pointBounds53208 := by
 decide +kernel
def cuts53209 : List PrefixCut := [⟨61,219026077,219026205⟩,
⟨64,230078117,230078251⟩]
theorem checked53209 : checkPrefixCuts (2^48) 6978142209 10 Manual.Count131072.C053209.packed 64 cuts53209 = true := by
 decide +kernel
def pointBounds53209 : List (Nat × Nat × Nat) := [(6978267136,112430134370290,112430521931890)]
theorem point_links_checked53209 : (cuts53209.take 1).map (fun c => (6978142209-1+2*2^10*c.k,112429915344213+c.lower,112430302905685+c.upper)) = pointBounds53209 := by
 decide +kernel
def cuts53210 : List PrefixCut := [⟨64,234430023,234430151⟩]
theorem checked53210 : checkPrefixCuts (2^48) 6978273281 10 Manual.Count131072.C053210.packed 64 cuts53210 = true := by
 decide +kernel
def cuts53211 : List PrefixCut := [⟨40,148271089,148271174⟩,
⟨64,237208707,237208840⟩]
theorem checked53211 : checkPrefixCuts (2^48) 6978404353 10 Manual.Count131072.C053211.packed 64 cuts53211 = true := by
 decide +kernel
def pointBounds53211 : List (Nat × Nat × Nat) := [(6978486272,112430528123442,112430915685261)]
theorem point_links_checked53211 : (cuts53211.take 1).map (fun c => (6978404353-1+2*2^10*c.k,112430379852353+c.lower,112430767414087+c.upper)) = pointBounds53211 := by
 decide +kernel
def cuts53212 : List PrefixCut := [⟨64,230468483,230468615⟩]
theorem checked53212 : checkPrefixCuts (2^48) 6978535425 10 Manual.Count131072.C053212.packed 64 cuts53212 = true := by
 decide +kernel
def cuts53213 : List PrefixCut := [⟨19,67961965,67962004⟩,
⟨64,233126122,233126257⟩]
theorem checked53213 : checkPrefixCuts (2^48) 6978666497 10 Manual.Count131072.C053213.packed 64 cuts53213 = true := by
 decide +kernel
def pointBounds53213 : List (Nat × Nat × Nat) := [(6978705408,112430915491508,112431303053546)]
theorem point_links_checked53213 : (cuts53213.take 1).map (fun c => (6978666497-1+2*2^10*c.k,112430847529543+c.lower,112431235091542+c.upper)) = pointBounds53213 := by
 decide +kernel
def cuts53214 : List PrefixCut := [⟨62,226103969,226104100⟩,
⟨64,233242754,233242889⟩]
theorem checked53214 : checkPrefixCuts (2^48) 6978797569 10 Manual.Count131072.C053214.packed 64 cuts53214 = true := by
 decide +kernel
def pointBounds53214 : List (Nat × Nat × Nat) := [(6978924544,112431306759634,112431694321899)]
theorem point_links_checked53214 : (cuts53214.take 1).map (fun c => (6978797569-1+2*2^10*c.k,112431080655665+c.lower,112431468217799+c.upper)) = pointBounds53214 := by
 decide +kernel
def cuts53215 : List PrefixCut := [⟨64,229084207,229084340⟩]
theorem checked53215 : checkPrefixCuts (2^48) 6978928641 10 Manual.Count131072.C053215.packed 64 cuts53215 = true := by
 decide +kernel
def cuts53216 : List PrefixCut := [⟨41,151281993,151282079⟩,
⟨64,236218507,236218641⟩]
theorem checked53216 : checkPrefixCuts (2^48) 6979059713 10 Manual.Count131072.C053216.packed 64 cuts53216 = true := by
 decide +kernel
def pointBounds53216 : List (Nat × Nat × Nat) := [(6979143680,112431694264619,112432081827107)]
theorem point_links_checked53216 : (cuts53216.take 1).map (fun c => (6979059713-1+2*2^10*c.k,112431542982626+c.lower,112431930545028+c.upper)) = pointBounds53216 := by
 decide +kernel
def cuts53217 : List PrefixCut := [⟨64,233592592,233592723⟩]
theorem checked53217 : checkPrefixCuts (2^48) 6979190785 10 Manual.Count131072.C053217.packed 64 cuts53217 = true := by
 decide +kernel
def cuts53218 : List PrefixCut := [⟨20,73763049,73763091⟩,
⟨64,234999736,234999869⟩]
theorem checked53218 : checkPrefixCuts (2^48) 6979321857 10 Manual.Count131072.C053218.packed 64 cuts53218 = true := by
 decide +kernel
def pointBounds53218 : List (Nat × Nat × Nat) := [(6979362816,112432086556774,112432474119483)]
theorem point_links_checked53218 : (cuts53218.take 1).map (fun c => (6979321857-1+2*2^10*c.k,112432012793725+c.lower,112432400356392+c.upper)) = pointBounds53218 := by
 decide +kernel
def cuts53219 : List PrefixCut := [⟨63,233745175,233745310⟩,
⟨64,237334396,237334533⟩]
theorem checked53219 : checkPrefixCuts (2^48) 6979452929 10 Manual.Count131072.C053219.packed 64 cuts53219 = true := by
 decide +kernel
def pointBounds53219 : List (Nat × Nat × Nat) := [(6979581952,112432481538636,112432869101571)]
theorem point_links_checked53219 : (cuts53219.take 1).map (fun c => (6979452929-1+2*2^10*c.k,112432247793461+c.lower,112432635356261+c.upper)) = pointBounds53219 := by
 decide +kernel
def cuts53220 : List PrefixCut := [⟨64,233458447,233458579⟩]
theorem checked53220 : checkPrefixCuts (2^48) 6979584001 10 Manual.Count131072.C053220.packed 64 cuts53220 = true := by
 decide +kernel
def cuts53221 : List PrefixCut := [⟨42,154251980,154252067⟩,
⟨64,233857354,233857486⟩]
theorem checked53221 : checkPrefixCuts (2^48) 6979715073 10 Manual.Count131072.C053221.packed 64 cuts53221 = true := by
 decide +kernel
def pointBounds53221 : List (Nat × Nat × Nat) := [(6979801088,112432872838284,112433260401440)]
theorem point_links_checked53221 : (cuts53221.take 1).map (fun c => (6979715073-1+2*2^10*c.k,112432718586304+c.lower,112433106149373+c.upper)) = pointBounds53221 := by
 decide +kernel
def cuts53222 : List PrefixCut := [⟨64,235062745,235062875⟩]
theorem checked53222 : checkPrefixCuts (2^48) 6979846145 10 Manual.Count131072.C053222.packed 64 cuts53222 = true := by
 decide +kernel
def cuts53223 : List PrefixCut := [⟨21,77627406,77627448⟩,
⟨64,231550009,231550140⟩]
theorem checked53223 : checkPrefixCuts (2^48) 6979977217 10 Manual.Count131072.C053223.packed 64 cuts53223 = true := by
 decide +kernel
def pointBounds53223 : List (Nat × Nat × Nat) := [(6980020224,112433265133809,112433652697182)]
theorem point_links_checked53223 : (cuts53223.take 1).map (fun c => (6979977217-1+2*2^10*c.k,112433187506403+c.lower,112433575069734+c.upper)) = pointBounds53223 := by
 decide +kernel
def cuts53224 : List PrefixCut := [⟨64,230134246,230134379⟩]
theorem checked53224 : checkPrefixCuts (2^48) 6980108289 10 Manual.Count131072.C053224.packed 64 cuts53224 = true := by
 decide +kernel
def pointBounds53224 : List (Nat × Nat × Nat) := [(6980239360,112433649190658,112434036754253)]
theorem point_links_checked53224 : (cuts53224.take 1).map (fun c => (6980108289-1+2*2^10*c.k,112433419056412+c.lower,112433806619874+c.upper)) = pointBounds53224 := by
 decide +kernel
def cuts53225 : List PrefixCut := [⟨64,237589927,237590060⟩]
theorem checked53225 : checkPrefixCuts (2^48) 6980239361 10 Manual.Count131072.C053225.packed 64 cuts53225 = true := by
 decide +kernel
def cuts53226 : List PrefixCut := [⟨43,155729433,155729521⟩,
⟨64,231738557,231738689⟩]
theorem checked53226 : checkPrefixCuts (2^48) 6980370433 10 Manual.Count131072.C053226.packed 64 cuts53226 = true := by
 decide +kernel
def pointBounds53226 : List (Nat × Nat × Nat) := [(6980458496,112434042510018,112434430073834)]
theorem point_links_checked53226 : (cuts53226.take 1).map (fun c => (6980370433-1+2*2^10*c.k,112433886780585+c.lower,112434274344313+c.upper)) = pointBounds53226 := by
 decide +kernel
def cuts53227 : List PrefixCut := [⟨64,235806794,235806927⟩]
theorem checked53227 : checkPrefixCuts (2^48) 6980501505 10 Manual.Count131072.C053227.packed 64 cuts53227 = true := by
 decide +kernel
def cuts53228 : List PrefixCut := [⟨22,79232989,79233034⟩,
⟨64,230036355,230036489⟩]
theorem checked53228 : checkPrefixCuts (2^48) 6980632577 10 Manual.Count131072.C053228.packed 64 cuts53228 = true := by
 decide +kernel
def pointBounds53228 : List (Nat × Nat × Nat) := [(6980677632,112434433558925,112434821122963)]
theorem point_links_checked53228 : (cuts53228.take 1).map (fun c => (6980632577-1+2*2^10*c.k,112434354325936+c.lower,112434741889929+c.upper)) = pointBounds53228 := by
 decide +kernel
def cuts53229 : List PrefixCut := [⟨64,232128716,232128848⟩]
theorem checked53229 : checkPrefixCuts (2^48) 6980763649 10 Manual.Count131072.C053229.packed 64 cuts53229 = true := by
 decide +kernel
def cuts53230 : List PrefixCut := [⟨1,3185339,3185340⟩,
⟨64,235511278,235511409⟩]
theorem checked53230 : checkPrefixCuts (2^48) 6980894721 10 Manual.Count131072.C053230.packed 64 cuts53230 = true := by
 decide +kernel
def pointBounds53230 : List (Nat × Nat × Nat) := [(6980896768,112434819676346,112435207240606)]
theorem point_links_checked53230 : (cuts53230.take 1).map (fun c => (6980894721-1+2*2^10*c.k,112434816491007+c.lower,112435204055266+c.upper)) = pointBounds53230 := by
 decide +kernel
def cuts53231 : List PrefixCut := [⟨44,159746770,159746863⟩,
⟨64,233894060,233894193⟩]
theorem checked53231 : checkPrefixCuts (2^48) 6981025793 10 Manual.Count131072.C053231.packed 64 cuts53231 = true := by
 decide +kernel
def pointBounds53231 : List (Nat × Nat × Nat) := [(6981115904,112435211749055,112435599313538)]
theorem point_links_checked53231 : (cuts53231.take 1).map (fun c => (6981025793-1+2*2^10*c.k,112435052002285+c.lower,112435439566675+c.upper)) = pointBounds53231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000100
