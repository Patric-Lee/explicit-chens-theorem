import PlattAssemblyKernel
import PlattCertificates.Count131072.C067392
import PlattCertificates.Count131072.C067393
import PlattCertificates.Count131072.C067394
import PlattCertificates.Count131072.C067395
import PlattCertificates.Count131072.C067396
import PlattCertificates.Count131072.C067397
import PlattCertificates.Count131072.C067398
import PlattCertificates.Count131072.C067399
import PlattCertificates.Count131072.C067400
import PlattCertificates.Count131072.C067401
import PlattCertificates.Count131072.C067402
import PlattCertificates.Count131072.C067403
import PlattCertificates.Count131072.C067404
import PlattCertificates.Count131072.C067405
import PlattCertificates.Count131072.C067406
import PlattCertificates.Count131072.C067407
import PlattCertificates.Count131072.C067408
import PlattCertificates.Count131072.C067409
import PlattCertificates.Count131072.C067410
import PlattCertificates.Count131072.C067411
import PlattCertificates.Count131072.C067412
import PlattCertificates.Count131072.C067413
import PlattCertificates.Count131072.C067414
import PlattCertificates.Count131072.C067415
import PlattCertificates.Count131072.C067416
import PlattCertificates.Count131072.C067417
import PlattCertificates.Count131072.C067418
import PlattCertificates.Count131072.C067419
import PlattCertificates.Count131072.C067420
import PlattCertificates.Count131072.C067421
import PlattCertificates.Count131072.C067422
import PlattCertificates.Count131072.C067423
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000231
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67392 : List PrefixCut := [⟨64,181615151,181615254⟩]
theorem checked67392 : checkPrefixCuts (2^48) 8837136385 10 Manual.Count131072.C067392.packed 64 cuts67392 = true := by
 decide +kernel
def cuts67393 : List PrefixCut := [⟨64,181612462,181612572⟩]
theorem checked67393 : checkPrefixCuts (2^48) 8837267457 10 Manual.Count131072.C067393.packed 64 cuts67393 = true := by
 decide +kernel
def cuts67394 : List PrefixCut := [⟨2,5446421,5446425⟩,
⟨64,182915616,182915725⟩]
theorem checked67394 : checkPrefixCuts (2^48) 8837398529 10 Manual.Count131072.C067394.packed 64 cuts67394 = true := by
 decide +kernel
def pointBounds67394 : List (Nat × Nat × Nat) := [(8837402624,115348066183121,115348455415391)]
theorem point_links_checked67394 : (cuts67394.take 1).map (fun c => (8837398529-1+2*2^10*c.k,115348060736700+c.lower,115348449968966+c.upper)) = pointBounds67394 := by
 decide +kernel
def cuts67395 : List PrefixCut := [⟨64,182530723,182530831⟩]
theorem checked67395 : checkPrefixCuts (2^48) 8837529601 10 Manual.Count131072.C067395.packed 64 cuts67395 = true := by
 decide +kernel
def cuts67396 : List PrefixCut := [⟨9,25415859,25415875⟩,
⟨64,181859176,181859281⟩]
theorem checked67396 : checkPrefixCuts (2^48) 8837660673 10 Manual.Count131072.C067396.packed 64 cuts67396 = true := by
 decide +kernel
def pointBounds67396 : List (Nat × Nat × Nat) := [(8837679104,115348451598898,115348840831397)]
theorem point_links_checked67396 : (cuts67396.take 1).map (fun c => (8837660673-1+2*2^10*c.k,115348426183039+c.lower,115348815415522+c.upper)) = pointBounds67396 := by
 decide +kernel
def cuts67397 : List PrefixCut := [⟨64,182684545,182684643⟩]
theorem checked67397 : checkPrefixCuts (2^48) 8837791745 10 Manual.Count131072.C067397.packed 64 cuts67397 = true := by
 decide +kernel
def cuts67398 : List PrefixCut := [⟨16,46275837,46275862⟩,
⟨64,181853794,181853901⟩]
theorem checked67398 : checkPrefixCuts (2^48) 8837922817 10 Manual.Count131072.C067398.packed 64 cuts67398 = true := by
 decide +kernel
def pointBounds67398 : List (Nat × Nat × Nat) := [(8837955584,115348837002597,115349226235308)]
theorem point_links_checked67398 : (cuts67398.take 1).map (fun c => (8837922817-1+2*2^10*c.k,115348790726760+c.lower,115349179959446+c.upper)) = pointBounds67398 := by
 decide +kernel
def cuts67399 : List PrefixCut := [⟨64,182806532,182806638⟩]
theorem checked67399 : checkPrefixCuts (2^48) 8838053889 10 Manual.Count131072.C067399.packed 64 cuts67399 = true := by
 decide +kernel
def cuts67400 : List PrefixCut := [⟨23,65637708,65637747⟩,
⟨64,182994890,182994993⟩]
theorem checked67400 : checkPrefixCuts (2^48) 8838184961 10 Manual.Count131072.C067400.packed 64 cuts67400 = true := by
 decide +kernel
def pointBounds67400 : List (Nat × Nat × Nat) := [(8838232064,115349221024794,115349610257732)]
theorem point_links_checked67400 : (cuts67400.take 1).map (fun c => (8838184961-1+2*2^10*c.k,115349155387086+c.lower,115349544619985+c.upper)) = pointBounds67400 := by
 decide +kernel
def cuts67401 : List PrefixCut := [⟨64,183692817,183692923⟩]
theorem checked67401 : checkPrefixCuts (2^48) 8838316033 10 Manual.Count131072.C067401.packed 64 cuts67401 = true := by
 decide +kernel
def cuts67402 : List PrefixCut := [⟨30,87928287,87928335⟩,
⟨64,185377967,185378071⟩]
theorem checked67402 : checkPrefixCuts (2^48) 8838447105 10 Manual.Count131072.C067402.packed 64 cuts67402 = true := by
 decide +kernel
def pointBounds67402 : List (Nat × Nat × Nat) := [(8838508544,115349610003080,115349999236236)]
theorem point_links_checked67402 : (cuts67402.take 1).map (fun c => (8838447105-1+2*2^10*c.k,115349522074793+c.lower,115349911307901+c.upper)) = pointBounds67402 := by
 decide +kernel
def cuts67403 : List PrefixCut := [⟨64,180662009,180662109⟩]
theorem checked67403 : checkPrefixCuts (2^48) 8838578177 10 Manual.Count131072.C067403.packed 64 cuts67403 = true := by
 decide +kernel
def cuts67404 : List PrefixCut := [⟨37,106396039,106396100⟩,
⟨64,182952209,182952316⟩]
theorem checked67404 : checkPrefixCuts (2^48) 8838709249 10 Manual.Count131072.C067404.packed 64 cuts67404 = true := by
 decide +kernel
def pointBounds67404 : List (Nat × Nat × Nat) := [(8838785024,115349994510808,115350383744181)]
theorem point_links_checked67404 : (cuts67404.take 1).map (fun c => (8838709249-1+2*2^10*c.k,115349888114769+c.lower,115350277348081+c.upper)) = pointBounds67404 := by
 decide +kernel
def cuts67405 : List PrefixCut := [⟨64,182981340,182981445⟩]
theorem checked67405 : checkPrefixCuts (2^48) 8838840321 10 Manual.Count131072.C067405.packed 64 cuts67405 = true := by
 decide +kernel
def cuts67406 : List PrefixCut := [⟨44,124162069,124162144⟩,
⟨64,181768509,181768619⟩]
theorem checked67406 : checkPrefixCuts (2^48) 8838971393 10 Manual.Count131072.C067406.packed 64 cuts67406 = true := by
 decide +kernel
def pointBounds67406 : List (Nat × Nat × Nat) := [(8839061504,115350378210387,115350767443986)]
theorem point_links_checked67406 : (cuts67406.take 1).map (fun c => (8838971393-1+2*2^10*c.k,115350254048318+c.lower,115350643281842+c.upper)) = pointBounds67406 := by
 decide +kernel
def cuts67407 : List PrefixCut := [⟨64,185746321,185746429⟩]
theorem checked67407 : checkPrefixCuts (2^48) 8839102465 10 Manual.Count131072.C067407.packed 64 cuts67407 = true := by
 decide +kernel
def cuts67408 : List PrefixCut := [⟨51,145175070,145175160⟩,
⟨64,182845798,182845911⟩]
theorem checked67408 : checkPrefixCuts (2^48) 8839233537 10 Manual.Count131072.C067408.packed 64 cuts67408 = true := by
 decide +kernel
def pointBounds67408 : List (Nat × Nat × Nat) := [(8839337984,115350766738218,115351155972050)]
theorem point_links_checked67408 : (cuts67408.take 1).map (fun c => (8839233537-1+2*2^10*c.k,115350621563148+c.lower,115351010796890+c.upper)) = pointBounds67408 := by
 decide +kernel
def cuts67409 : List PrefixCut := [⟨64,181824122,181824231⟩]
theorem checked67409 : checkPrefixCuts (2^48) 8839364609 10 Manual.Count131072.C067409.packed 64 cuts67409 = true := by
 decide +kernel
def cuts67410 : List PrefixCut := [⟨58,165263367,165263467⟩,
⟨64,183158806,183158918⟩]
theorem checked67410 : checkPrefixCuts (2^48) 8839495681 10 Manual.Count131072.C067410.packed 64 cuts67410 = true := by
 decide +kernel
def pointBounds67410 : List (Nat × Nat × Nat) := [(8839614464,115351151496435,115351540730499)]
theorem point_links_checked67410 : (cuts67410.take 1).map (fun c => (8839495681-1+2*2^10*c.k,115350986233068+c.lower,115351375467032+c.upper)) = pointBounds67410 := by
 decide +kernel
def cuts67411 : List PrefixCut := [⟨64,181914257,181914366⟩]
theorem checked67411 : checkPrefixCuts (2^48) 8839626753 10 Manual.Count131072.C067411.packed 64 cuts67411 = true := by
 decide +kernel
def cuts67412 : List PrefixCut := [⟨64,183408126,183408228⟩]
theorem checked67412 : checkPrefixCuts (2^48) 8839757825 10 Manual.Count131072.C067412.packed 64 cuts67412 = true := by
 decide +kernel
def cuts67413 : List PrefixCut := [⟨1,2515474,2515476⟩,
⟨64,182800414,182800522⟩]
theorem checked67413 : checkPrefixCuts (2^48) 8839888897 10 Manual.Count131072.C067413.packed 64 cuts67413 = true := by
 decide +kernel
def pointBounds67413 : List (Nat × Nat × Nat) := [(8839890944,115351537229731,115351926464020)]
theorem point_links_checked67413 : (cuts67413.take 1).map (fun c => (8839888897-1+2*2^10*c.k,115351534714257+c.lower,115351923948544+c.upper)) = pointBounds67413 := by
 decide +kernel
def cuts67414 : List PrefixCut := [⟨64,181396713,181396824⟩]
theorem checked67414 : checkPrefixCuts (2^48) 8840019969 10 Manual.Count131072.C067414.packed 64 cuts67414 = true := by
 decide +kernel
def cuts67415 : List PrefixCut := [⟨8,22797783,22797796⟩,
⟨64,179260724,179260830⟩]
theorem checked67415 : checkPrefixCuts (2^48) 8840151041 10 Manual.Count131072.C067415.packed 64 cuts67415 = true := by
 decide +kernel
def pointBounds67415 : List (Nat × Nat × Nat) := [(8840167424,115351921709167,115352310943686)]
theorem point_links_checked67415 : (cuts67415.take 1).map (fun c => (8840151041-1+2*2^10*c.k,115351898911384+c.lower,115352288145890+c.upper)) = pointBounds67415 := by
 decide +kernel
def cuts67416 : List PrefixCut := [⟨64,181900756,181900858⟩]
theorem checked67416 : checkPrefixCuts (2^48) 8840282113 10 Manual.Count131072.C067416.packed 64 cuts67416 = true := by
 decide +kernel
def cuts67417 : List PrefixCut := [⟨15,42219186,42219214⟩,
⟨64,181675191,181675301⟩]
theorem checked67417 : checkPrefixCuts (2^48) 8840413185 10 Manual.Count131072.C067417.packed 64 cuts67417 = true := by
 decide +kernel
def pointBounds67417 : List (Nat × Nat × Nat) := [(8840443904,115352302292050,115352691526792)]
theorem point_links_checked67417 : (cuts67417.take 1).map (fun c => (8840413185-1+2*2^10*c.k,115352260072864+c.lower,115352649307578+c.upper)) = pointBounds67417 := by
 decide +kernel
def cuts67418 : List PrefixCut := [⟨64,184792716,184792825⟩]
theorem checked67418 : checkPrefixCuts (2^48) 8840544257 10 Manual.Count131072.C067418.packed 64 cuts67418 = true := by
 decide +kernel
def cuts67419 : List PrefixCut := [⟨22,63963623,63963662⟩,
⟨64,182147406,182147513⟩]
theorem checked67419 : checkPrefixCuts (2^48) 8840675329 10 Manual.Count131072.C067419.packed 64 cuts67419 = true := by
 decide +kernel
def pointBounds67419 : List (Nat × Nat × Nat) := [(8840720384,115352690504394,115353079739366)]
theorem point_links_checked67419 : (cuts67419.take 1).map (fun c => (8840675329-1+2*2^10*c.k,115352626540771+c.lower,115353015775704+c.upper)) = pointBounds67419 := by
 decide +kernel
def cuts67420 : List PrefixCut := [⟨64,181380588,181380691⟩]
theorem checked67420 : checkPrefixCuts (2^48) 8840806401 10 Manual.Count131072.C067420.packed 64 cuts67420 = true := by
 decide +kernel
def cuts67421 : List PrefixCut := [⟨29,82905025,82905072⟩,
⟨64,183733855,183733959⟩]
theorem checked67421 : checkPrefixCuts (2^48) 8840937473 10 Manual.Count131072.C067421.packed 64 cuts67421 = true := by
 decide +kernel
def pointBounds67421 : List (Nat × Nat × Nat) := [(8840996864,115353072973790,115353462208980)]
theorem point_links_checked67421 : (cuts67421.take 1).map (fun c => (8840937473-1+2*2^10*c.k,115352990068765+c.lower,115353379303908+c.upper)) = pointBounds67421 := by
 decide +kernel
def cuts67422 : List PrefixCut := [⟨64,179242110,179242220⟩]
theorem checked67422 : checkPrefixCuts (2^48) 8841068545 10 Manual.Count131072.C067422.packed 64 cuts67422 = true := by
 decide +kernel
def cuts67423 : List PrefixCut := [⟨36,101463236,101463294⟩,
⟨64,180417412,180417517⟩]
theorem checked67423 : checkPrefixCuts (2^48) 8841199617 10 Manual.Count131072.C067423.packed 64 cuts67423 = true := by
 decide +kernel
def pointBounds67423 : List (Nat × Nat × Nat) := [(8841273344,115353454507966,115353843743381)]
theorem point_links_checked67423 : (cuts67423.take 1).map (fun c => (8841199617-1+2*2^10*c.k,115353353044730+c.lower,115353742280087+c.upper)) = pointBounds67423 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000231
