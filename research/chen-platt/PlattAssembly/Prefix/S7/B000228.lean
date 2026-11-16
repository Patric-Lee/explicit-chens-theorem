import PlattAssemblyKernel
import PlattCertificates.Count131072.C067296
import PlattCertificates.Count131072.C067297
import PlattCertificates.Count131072.C067298
import PlattCertificates.Count131072.C067299
import PlattCertificates.Count131072.C067300
import PlattCertificates.Count131072.C067301
import PlattCertificates.Count131072.C067302
import PlattCertificates.Count131072.C067303
import PlattCertificates.Count131072.C067304
import PlattCertificates.Count131072.C067305
import PlattCertificates.Count131072.C067306
import PlattCertificates.Count131072.C067307
import PlattCertificates.Count131072.C067308
import PlattCertificates.Count131072.C067309
import PlattCertificates.Count131072.C067310
import PlattCertificates.Count131072.C067311
import PlattCertificates.Count131072.C067312
import PlattCertificates.Count131072.C067313
import PlattCertificates.Count131072.C067314
import PlattCertificates.Count131072.C067315
import PlattCertificates.Count131072.C067316
import PlattCertificates.Count131072.C067317
import PlattCertificates.Count131072.C067318
import PlattCertificates.Count131072.C067319
import PlattCertificates.Count131072.C067320
import PlattCertificates.Count131072.C067321
import PlattCertificates.Count131072.C067322
import PlattCertificates.Count131072.C067323
import PlattCertificates.Count131072.C067324
import PlattCertificates.Count131072.C067325
import PlattCertificates.Count131072.C067326
import PlattCertificates.Count131072.C067327
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000228
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67296 : List PrefixCut := [⟨64,182639638,182639743⟩]
theorem checked67296 : checkPrefixCuts (2^48) 8824553473 10 Manual.Count131072.C067296.packed 64 cuts67296 = true := by
 decide +kernel
def pointBounds67296 : List (Nat × Nat × Nat) := [(8824684544,115330362058352,115330751280328)]
theorem point_links_checked67296 : (cuts67296.take 1).map (fun c => (8824553473-1+2*2^10*c.k,115330179418714+c.lower,115330568640585+c.upper)) = pointBounds67296 := by
 decide +kernel
def cuts67297 : List PrefixCut := [⟨64,181775748,181775857⟩]
theorem checked67297 : checkPrefixCuts (2^48) 8824684545 10 Manual.Count131072.C067297.packed 64 cuts67297 = true := by
 decide +kernel
def cuts67298 : List PrefixCut := [⟨64,182442841,182442945⟩]
theorem checked67298 : checkPrefixCuts (2^48) 8824815617 10 Manual.Count131072.C067298.packed 64 cuts67298 = true := by
 decide +kernel
def cuts67299 : List PrefixCut := [⟨7,20572495,20572506⟩,
⟨64,180526444,180526546⟩]
theorem checked67299 : checkPrefixCuts (2^48) 8824946689 10 Manual.Count131072.C067299.packed 64 cuts67299 = true := by
 decide +kernel
def pointBounds67299 : List (Nat × Nat × Nat) := [(8824961024,115330746849436,115331136071636)]
theorem point_links_checked67299 : (cuts67299.take 1).map (fun c => (8824946689-1+2*2^10*c.k,115330726276941+c.lower,115331115499130+c.upper)) = pointBounds67299 := by
 decide +kernel
def cuts67300 : List PrefixCut := [⟨64,182277953,182278057⟩]
theorem checked67300 : checkPrefixCuts (2^48) 8825077761 10 Manual.Count131072.C067300.packed 64 cuts67300 = true := by
 decide +kernel
def cuts67301 : List PrefixCut := [⟨14,40697211,40697236⟩,
⟨64,182849335,182849443⟩]
theorem checked67301 : checkPrefixCuts (2^48) 8825208833 10 Manual.Count131072.C067301.packed 64 cuts67301 = true := by
 decide +kernel
def pointBounds67301 : List (Nat × Nat × Nat) := [(8825237504,115331129778549,115331519000969)]
theorem point_links_checked67301 : (cuts67301.take 1).map (fun c => (8825208833-1+2*2^10*c.k,115331089081338+c.lower,115331478303733+c.upper)) = pointBounds67301 := by
 decide +kernel
def cuts67302 : List PrefixCut := [⟨64,183771536,183771638⟩]
theorem checked67302 : checkPrefixCuts (2^48) 8825339905 10 Manual.Count131072.C067302.packed 64 cuts67302 = true := by
 decide +kernel
def cuts67303 : List PrefixCut := [⟨21,59927685,59927720⟩,
⟨64,184470450,184470561⟩]
theorem checked67303 : checkPrefixCuts (2^48) 8825470977 10 Manual.Count131072.C067303.packed 64 cuts67303 = true := by
 decide +kernel
def pointBounds67303 : List (Nat × Nat × Nat) := [(8825513984,115331515629894,115331904852534)]
theorem point_links_checked67303 : (cuts67303.take 1).map (fun c => (8825470977-1+2*2^10*c.k,115331455702209+c.lower,115331844924814+c.upper)) = pointBounds67303 := by
 decide +kernel
def cuts67304 : List PrefixCut := [⟨64,183638510,183638617⟩]
theorem checked67304 : checkPrefixCuts (2^48) 8825602049 10 Manual.Count131072.C067304.packed 64 cuts67304 = true := by
 decide +kernel
def cuts67305 : List PrefixCut := [⟨28,78838065,78838103⟩,
⟨64,182966043,182966143⟩]
theorem checked67305 : checkPrefixCuts (2^48) 8825733121 10 Manual.Count131072.C067305.packed 64 cuts67305 = true := by
 decide +kernel
def pointBounds67305 : List (Nat × Nat × Nat) := [(8825790464,115331902649234,115332291872095)]
theorem point_links_checked67305 : (cuts67305.take 1).map (fun c => (8825733121-1+2*2^10*c.k,115331823811169+c.lower,115332213033992+c.upper)) = pointBounds67305 := by
 decide +kernel
def cuts67306 : List PrefixCut := [⟨64,183218464,183218573⟩]
theorem checked67306 : checkPrefixCuts (2^48) 8825864193 10 Manual.Count131072.C067306.packed 64 cuts67306 = true := by
 decide +kernel
def cuts67307 : List PrefixCut := [⟨35,99596986,99597050⟩,
⟨64,182290887,182290998⟩]
theorem checked67307 : checkPrefixCuts (2^48) 8825995265 10 Manual.Count131072.C067307.packed 64 cuts67307 = true := by
 decide +kernel
def pointBounds67307 : List (Nat × Nat × Nat) := [(8826066944,115332289592662,115332678815758)]
theorem point_links_checked67307 : (cuts67307.take 1).map (fun c => (8825995265-1+2*2^10*c.k,115332189995676+c.lower,115332579218708+c.upper)) = pointBounds67307 := by
 decide +kernel
def cuts67308 : List PrefixCut := [⟨64,184233536,184233641⟩]
theorem checked67308 : checkPrefixCuts (2^48) 8826126337 10 Manual.Count131072.C067308.packed 64 cuts67308 = true := by
 decide +kernel
def cuts67309 : List PrefixCut := [⟨42,120227081,120227151⟩,
⟨64,183178408,183178513⟩]
theorem checked67309 : checkPrefixCuts (2^48) 8826257409 10 Manual.Count131072.C067309.packed 64 cuts67309 = true := by
 decide +kernel
def pointBounds67309 : List (Nat × Nat × Nat) := [(8826343424,115332676747180,115333065970498)]
theorem point_links_checked67309 : (cuts67309.take 1).map (fun c => (8826257409-1+2*2^10*c.k,115332556520099+c.lower,115332945743347+c.upper)) = pointBounds67309 := by
 decide +kernel
def cuts67310 : List PrefixCut := [⟨64,182474112,182474218⟩]
theorem checked67310 : checkPrefixCuts (2^48) 8826388481 10 Manual.Count131072.C067310.packed 64 cuts67310 = true := by
 decide +kernel
def cuts67311 : List PrefixCut := [⟨49,140058685,140058769⟩,
⟨64,183236746,183236857⟩]
theorem checked67311 : checkPrefixCuts (2^48) 8826519553 10 Manual.Count131072.C067311.packed 64 cuts67311 = true := by
 decide +kernel
def pointBounds67311 : List (Nat × Nat × Nat) := [(8826619904,115333062231304,115333451454847)]
theorem point_links_checked67311 : (cuts67311.take 1).map (fun c => (8826519553-1+2*2^10*c.k,115332922172619+c.lower,115333311396078+c.upper)) = pointBounds67311 := by
 decide +kernel
def cuts67312 : List PrefixCut := [⟨64,183297805,183297915⟩]
theorem checked67312 : checkPrefixCuts (2^48) 8826650625 10 Manual.Count131072.C067312.packed 64 cuts67312 = true := by
 decide +kernel
def cuts67313 : List PrefixCut := [⟨56,159346969,159347059⟩,
⟨64,181636883,181636987⟩]
theorem checked67313 : checkPrefixCuts (2^48) 8826781697 10 Manual.Count131072.C067313.packed 64 cuts67313 = true := by
 decide +kernel
def pointBounds67313 : List (Nat × Nat × Nat) := [(8826896384,115333448054139,115333837277909)]
theorem point_links_checked67313 : (cuts67313.take 1).map (fun c => (8826781697-1+2*2^10*c.k,115333288707170+c.lower,115333677930850+c.upper)) = pointBounds67313 := by
 decide +kernel
def cuts67314 : List PrefixCut := [⟨64,180549990,180550091⟩]
theorem checked67314 : checkPrefixCuts (2^48) 8826912769 10 Manual.Count131072.C067314.packed 64 cuts67314 = true := by
 decide +kernel
def cuts67315 : List PrefixCut := [⟨63,181408301,181408407⟩,
⟨64,184278160,184278267⟩]
theorem checked67315 : checkPrefixCuts (2^48) 8827043841 10 Manual.Count131072.C067315.packed 64 cuts67315 = true := by
 decide +kernel
def pointBounds67315 : List (Nat × Nat × Nat) := [(8827172864,115333832302344,115334221526335)]
theorem point_links_checked67315 : (cuts67315.take 1).map (fun c => (8827043841-1+2*2^10*c.k,115333650894043+c.lower,115334040117928+c.upper)) = pointBounds67315 := by
 decide +kernel
def cuts67316 : List PrefixCut := [⟨64,183382586,183382690⟩]
theorem checked67316 : checkPrefixCuts (2^48) 8827174913 10 Manual.Count131072.C067316.packed 64 cuts67316 = true := by
 decide +kernel
def cuts67317 : List PrefixCut := [⟨64,181562325,181562428⟩]
theorem checked67317 : checkPrefixCuts (2^48) 8827305985 10 Manual.Count131072.C067317.packed 64 cuts67317 = true := by
 decide +kernel
def cuts67318 : List PrefixCut := [⟨6,17696923,17696931⟩,
⟨64,182356783,182356889⟩]
theorem checked67318 : checkPrefixCuts (2^48) 8827437057 10 Manual.Count131072.C067318.packed 64 cuts67318 = true := by
 decide +kernel
def pointBounds67318 : List (Nat × Nat × Nat) := [(8827449344,115334217814037,115334607038244)]
theorem point_links_checked67318 : (cuts67318.take 1).map (fun c => (8827437057-1+2*2^10*c.k,115334200117114+c.lower,115334589341313+c.upper)) = pointBounds67318 := by
 decide +kernel
def cuts67319 : List PrefixCut := [⟨64,182513496,182513604⟩]
theorem checked67319 : checkPrefixCuts (2^48) 8827568129 10 Manual.Count131072.C067319.packed 64 cuts67319 = true := by
 decide +kernel
def cuts67320 : List PrefixCut := [⟨13,37656624,37656645⟩,
⟨64,183180381,183180484⟩]
theorem checked67320 : checkPrefixCuts (2^48) 8827699201 10 Manual.Count131072.C067320.packed 64 cuts67320 = true := by
 decide +kernel
def pointBounds67320 : List (Nat × Nat × Nat) := [(8827725824,115334602644017,115334991868451)]
theorem point_links_checked67320 : (cuts67320.take 1).map (fun c => (8827699201-1+2*2^10*c.k,115334564987393+c.lower,115334954211806+c.upper)) = pointBounds67320 := by
 decide +kernel
def cuts67321 : List PrefixCut := [⟨64,184070439,184070545⟩]
theorem checked67321 : checkPrefixCuts (2^48) 8827830273 10 Manual.Count131072.C067321.packed 64 cuts67321 = true := by
 decide +kernel
def cuts67322 : List PrefixCut := [⟨20,57232496,57232529⟩,
⟨64,182824213,182824319⟩]
theorem checked67322 : checkPrefixCuts (2^48) 8827961345 10 Manual.Count131072.C067322.packed 64 cuts67322 = true := by
 decide +kernel
def pointBounds67322 : List (Nat × Nat × Nat) := [(8828002304,115334989470709,115335378695364)]
theorem point_links_checked67322 : (cuts67322.take 1).map (fun c => (8827961345-1+2*2^10*c.k,115334932238213+c.lower,115335321462835+c.upper)) = pointBounds67322 := by
 decide +kernel
def cuts67323 : List PrefixCut := [⟨64,183554813,183554919⟩]
theorem checked67323 : checkPrefixCuts (2^48) 8828092417 10 Manual.Count131072.C067323.packed 64 cuts67323 = true := by
 decide +kernel
def cuts67324 : List PrefixCut := [⟨27,76679641,76679689⟩,
⟨64,184125992,184126100⟩]
theorem checked67324 : checkPrefixCuts (2^48) 8828223489 10 Manual.Count131072.C067324.packed 64 cuts67324 = true := by
 decide +kernel
def pointBounds67324 : List (Nat × Nat × Nat) := [(8828278784,115335375296880,115335764521762)]
theorem point_links_checked67324 : (cuts67324.take 1).map (fun c => (8828223489-1+2*2^10*c.k,115335298617239+c.lower,115335687842073+c.upper)) = pointBounds67324 := by
 decide +kernel
def cuts67325 : List PrefixCut := [⟨64,182847952,182848060⟩]
theorem checked67325 : checkPrefixCuts (2^48) 8828354561 10 Manual.Count131072.C067325.packed 64 cuts67325 = true := by
 decide +kernel
def cuts67326 : List PrefixCut := [⟨34,97050189,97050244⟩,
⟨64,182111946,182112048⟩]
theorem checked67326 : checkPrefixCuts (2^48) 8828485633 10 Manual.Count131072.C067326.packed 64 cuts67326 = true := by
 decide +kernel
def pointBounds67326 : List (Nat × Nat × Nat) := [(8828555264,115335762641372,115336151866477)]
theorem point_links_checked67326 : (cuts67326.take 1).map (fun c => (8828485633-1+2*2^10*c.k,115335665591183+c.lower,115336054816233+c.upper)) = pointBounds67326 := by
 decide +kernel
def cuts67327 : List PrefixCut := [⟨64,180132560,180132668⟩]
theorem checked67327 : checkPrefixCuts (2^48) 8828616705 10 Manual.Count131072.C067327.packed 64 cuts67327 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000228
