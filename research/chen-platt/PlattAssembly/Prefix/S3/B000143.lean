import PlattAssemblyKernel
import PlattCertificates.Count131072.C024576
import PlattCertificates.Count131072.C024577
import PlattCertificates.Count131072.C024578
import PlattCertificates.Count131072.C024579
import PlattCertificates.Count131072.C024580
import PlattCertificates.Count131072.C024581
import PlattCertificates.Count131072.C024582
import PlattCertificates.Count131072.C024583
import PlattCertificates.Count131072.C024584
import PlattCertificates.Count131072.C024585
import PlattCertificates.Count131072.C024586
import PlattCertificates.Count131072.C024587
import PlattCertificates.Count131072.C024588
import PlattCertificates.Count131072.C024589
import PlattCertificates.Count131072.C024590
import PlattCertificates.Count131072.C024591
import PlattCertificates.Count131072.C024592
import PlattCertificates.Count131072.C024593
import PlattCertificates.Count131072.C024594
import PlattCertificates.Count131072.C024595
import PlattCertificates.Count131072.C024596
import PlattCertificates.Count131072.C024597
import PlattCertificates.Count131072.C024598
import PlattCertificates.Count131072.C024599
import PlattCertificates.Count131072.C024600
import PlattCertificates.Count131072.C024601
import PlattCertificates.Count131072.C024602
import PlattCertificates.Count131072.C024603
import PlattCertificates.Count131072.C024604
import PlattCertificates.Count131072.C024605
import PlattCertificates.Count131072.C024606
import PlattCertificates.Count131072.C024607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000143
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24576 : List PrefixCut := [⟨81,322301579,322301767⟩,
⟨128,518226950,518227247⟩]
theorem checked24576 : checkPrefixCuts (2^48) 3225157633 9 Manual.Count131072.C024576.packed 128 cuts24576 = true := by
 decide +kernel
def pointBounds24576 : List (Nat × Nat × Nat) := [(3225240576,102678818439974,102679200333258)]
theorem point_links_checked24576 : (cuts24576.take 1).map (fun c => (3225157633-1+2*2^9*c.k,102678496138395+c.lower,102678878031491+c.upper)) = pointBounds24576 := by
 decide +kernel
def cuts24577 : List PrefixCut := [⟨52,207442004,207442119⟩,
⟨128,517769613,517769905⟩]
theorem checked24577 : checkPrefixCuts (2^48) 3225288705 9 Manual.Count131072.C024577.packed 128 cuts24577 = true := by
 decide +kernel
def pointBounds24577 : List (Nat × Nat × Nat) := [(3225341952,102679221807349,102679603700857)]
theorem point_links_checked24577 : (cuts24577.take 1).map (fun c => (3225288705-1+2*2^9*c.k,102679014365345+c.lower,102679396258738+c.upper)) = pointBounds24577 := by
 decide +kernel
def cuts24578 : List PrefixCut := [⟨23,94248752,94248804⟩,
⟨122,497328873,497329153⟩,
⟨128,521762855,521763148⟩]
theorem checked24578 : checkPrefixCuts (2^48) 3225419777 9 Manual.Count131072.C024578.packed 128 cuts24578 = true := by
 decide +kernel
def pointBounds24578 : List (Nat × Nat × Nat) := [(3225443328,102679626383710,102680008277447),(3225544704,102680029463831,102680411357796)]
theorem point_links_checked24578 : (cuts24578.take 2).map (fun c => (3225419777-1+2*2^9*c.k,102679532134958+c.lower,102679914028643+c.upper)) = pointBounds24578 := by
 decide +kernel
def cuts24579 : List PrefixCut := [⟨93,379331567,379331776⟩,
⟨128,527151835,527152127⟩]
theorem checked24579 : checkPrefixCuts (2^48) 3225550849 9 Manual.Count131072.C024579.packed 128 cuts24579 = true := by
 decide +kernel
def pointBounds24579 : List (Nat × Nat × Nat) := [(3225646080,102680433229380,102680815123567)]
theorem point_links_checked24579 : (cuts24579.take 1).map (fun c => (3225550849-1+2*2^9*c.k,102680053897813+c.lower,102680435791791+c.upper)) = pointBounds24579 := by
 decide +kernel
def cuts24580 : List PrefixCut := [⟨64,259335838,259335985⟩,
⟨128,521371382,521371681⟩]
theorem checked24580 : checkPrefixCuts (2^48) 3225681921 9 Manual.Count131072.C024580.packed 128 cuts24580 = true := by
 decide +kernel
def pointBounds24580 : List (Nat × Nat × Nat) := [(3225747456,102680840385486,102681222279903)]
theorem point_links_checked24580 : (cuts24580.take 1).map (fun c => (3225681921-1+2*2^9*c.k,102680581049648+c.lower,102680962943918+c.upper)) = pointBounds24580 := by
 decide +kernel
def cuts24581 : List PrefixCut := [⟨35,139435986,139436061⟩,
⟨128,520477710,520477997⟩]
theorem checked24581 : checkPrefixCuts (2^48) 3225812993 9 Manual.Count131072.C024581.packed 128 cuts24581 = true := by
 decide +kernel
def pointBounds24581 : List (Nat × Nat × Nat) := [(3225848832,102681241857016,102681623751660)]
theorem point_links_checked24581 : (cuts24581.take 1).map (fun c => (3225812993-1+2*2^9*c.k,102681102421030+c.lower,102681484315599+c.upper)) = pointBounds24581 := by
 decide +kernel
def cuts24582 : List PrefixCut := [⟨6,25739757,25739772⟩,
⟨105,429367324,429367570⟩,
⟨128,524033864,524034168⟩]
theorem checked24582 : checkPrefixCuts (2^48) 3225944065 9 Manual.Count131072.C024582.packed 128 cuts24582 = true := by
 decide +kernel
def pointBounds24582 : List (Nat × Nat × Nat) := [(3225950208,102681648638497,102682030533368),(3226051584,102682052266064,102682434161166)]
theorem point_links_checked24582 : (cuts24582.take 2).map (fun c => (3225944065-1+2*2^9*c.k,102681622898740+c.lower,102682004793596+c.upper)) = pointBounds24582 := by
 decide +kernel
def cuts24583 : List PrefixCut := [⟨76,311216845,311217017⟩,
⟨128,522703869,522704157⟩]
theorem checked24583 : checkPrefixCuts (2^48) 3226075137 9 Manual.Count131072.C024583.packed 128 cuts24583 = true := by
 decide +kernel
def pointBounds24583 : List (Nat × Nat × Nat) := [(3226152960,102682458149449,102682840044781)]
theorem point_links_checked24583 : (cuts24583.take 1).map (fun c => (3226075137-1+2*2^9*c.k,102682146932604+c.lower,102682528827764+c.upper)) = pointBounds24583 := by
 decide +kernel
def cuts24584 : List PrefixCut := [⟨47,197524403,197524511⟩,
⟨128,526608712,526609004⟩]
theorem checked24584 : checkPrefixCuts (2^48) 3226206209 9 Manual.Count131072.C024584.packed 128 cuts24584 = true := by
 decide +kernel
def pointBounds24584 : List (Nat × Nat × Nat) := [(3226254336,102682867160876,102683249056432)]
theorem point_links_checked24584 : (cuts24584.take 1).map (fun c => (3226206209-1+2*2^9*c.k,102682669636473+c.lower,102683051531921+c.upper)) = pointBounds24584 := by
 decide +kernel
def cuts24585 : List PrefixCut := [⟨18,73981742,73981780⟩,
⟨117,478082001,478082275⟩,
⟨128,524406159,524406457⟩]
theorem checked24585 : checkPrefixCuts (2^48) 3226337281 9 Manual.Count131072.C024585.packed 128 cuts24585 = true := by
 decide +kernel
def pointBounds24585 : List (Nat × Nat × Nat) := [(3226355712,102683270226927,102683652122705),(3226457088,102683674327186,102684056223200)]
theorem point_links_checked24585 : (cuts24585.take 2).map (fun c => (3226337281-1+2*2^9*c.k,102683196245185+c.lower,102683578140925+c.upper)) = pointBounds24585 := by
 decide +kernel
def cuts24586 : List PrefixCut := [⟨88,359857159,359857363⟩,
⟨128,524472105,524472397⟩]
theorem checked24586 : checkPrefixCuts (2^48) 3226468353 9 Manual.Count131072.C024586.packed 128 cuts24586 = true := by
 decide +kernel
def pointBounds24586 : List (Nat × Nat × Nat) := [(3226558464,102684080508503,102684462404745)]
theorem point_links_checked24586 : (cuts24586.take 1).map (fun c => (3226468353-1+2*2^9*c.k,102683720651344+c.lower,102684102547382+c.upper)) = pointBounds24586 := by
 decide +kernel
def cuts24587 : List PrefixCut := [⟨59,241466362,241466493⟩,
⟨128,524974204,524974492⟩]
theorem checked24587 : checkPrefixCuts (2^48) 3226599425 9 Manual.Count131072.C024587.packed 128 cuts24587 = true := by
 decide +kernel
def pointBounds24587 : List (Nat × Nat × Nat) := [(3226659840,102684486589811,102684868486272)]
theorem point_links_checked24587 : (cuts24587.take 1).map (fun c => (3226599425-1+2*2^9*c.k,102684245123449+c.lower,102684627019779+c.upper)) = pointBounds24587 := by
 decide +kernel
def cuts24588 : List PrefixCut := [⟨30,119856508,119856576⟩,
⟨128,517538300,517538585⟩]
theorem checked24588 : checkPrefixCuts (2^48) 3226730497 9 Manual.Count131072.C024588.packed 128 cuts24588 = true := by
 decide +kernel
def pointBounds24588 : List (Nat × Nat × Nat) := [(3226761216,102684889954161,102685271850847)]
theorem point_links_checked24588 : (cuts24588.take 1).map (fun c => (3226730497-1+2*2^9*c.k,102684770097653+c.lower,102685151994271+c.upper)) = pointBounds24588 := by
 decide +kernel
def cuts24589 : List PrefixCut := [⟨1,3401918,3401920⟩,
⟨100,402379544,402379776⟩,
⟨128,516121643,516121938⟩]
theorem checked24589 : checkPrefixCuts (2^48) 3226861569 9 Manual.Count131072.C024589.packed 128 cuts24589 = true := by
 decide +kernel
def pointBounds24589 : List (Nat × Nat × Nat) := [(3226862592,102685291037871,102685672934776),(3226963968,102685690015497,102686071912632)]
theorem point_links_checked24589 : (cuts24589.take 2).map (fun c => (3226861569-1+2*2^9*c.k,102685287635953+c.lower,102685669532856+c.upper)) = pointBounds24589 := by
 decide +kernel
def cuts24590 : List PrefixCut := [⟨71,287578065,287578224⟩,
⟨128,519415163,519415452⟩]
theorem checked24590 : checkPrefixCuts (2^48) 3226992641 9 Manual.Count131072.C024590.packed 128 cuts24590 = true := by
 decide +kernel
def pointBounds24590 : List (Nat × Nat × Nat) := [(3227065344,102686091335661,102686473233018)]
theorem point_links_checked24590 : (cuts24590.take 1).map (fun c => (3226992641-1+2*2^9*c.k,102685803757596+c.lower,102686185654794+c.upper)) = pointBounds24590 := by
 decide +kernel
def cuts24591 : List PrefixCut := [⟨42,171912623,171912719⟩,
⟨128,524627311,524627608⟩]
theorem checked24591 : checkPrefixCuts (2^48) 3227123713 9 Manual.Count131072.C024591.packed 128 cuts24591 = true := by
 decide +kernel
def pointBounds24591 : List (Nat × Nat × Nat) := [(3227166720,102686495085382,102686876982965)]
theorem point_links_checked24591 : (cuts24591.take 1).map (fun c => (3227123713-1+2*2^9*c.k,102686323172759+c.lower,102686705070246+c.upper)) = pointBounds24591 := by
 decide +kernel
def cuts24592 : List PrefixCut := [⟨13,52679596,52679625⟩,
⟨112,451083799,451084048⟩,
⟨128,518762431,518762717⟩]
theorem checked24592 : checkPrefixCuts (2^48) 3227254785 9 Manual.Count131072.C024592.packed 128 cuts24592 = true := by
 decide +kernel
def pointBounds24592 : List (Nat × Nat × Nat) := [(3227268096,102686900479666,102687282377479),(3227369472,102687298883869,102687680781902)]
theorem point_links_checked24592 : (cuts24592.take 2).map (fun c => (3227254785-1+2*2^9*c.k,102686847800070+c.lower,102687229697854+c.upper)) = pointBounds24592 := by
 decide +kernel
def cuts24593 : List PrefixCut := [⟨83,337864580,337864768⟩,
⟨128,519264702,519264994⟩]
theorem checked24593 : checkPrefixCuts (2^48) 3227385857 9 Manual.Count131072.C024593.packed 128 cuts24593 = true := by
 decide +kernel
def pointBounds24593 : List (Nat × Nat × Nat) := [(3227470848,102687704427081,102688086325339)]
theorem point_links_checked24593 : (cuts24593.take 1).map (fun c => (3227385857-1+2*2^9*c.k,102687366562501+c.lower,102687748460571+c.upper)) = pointBounds24593 := by
 decide +kernel
def cuts24594 : List PrefixCut := [⟨54,218984873,218984995⟩,
⟨128,520987744,520988036⟩]
theorem checked24594 : checkPrefixCuts (2^48) 3227516929 9 Manual.Count131072.C024594.packed 128 cuts24594 = true := by
 decide +kernel
def pointBounds24594 : List (Nat × Nat × Nat) := [(3227572224,102688104812076,102688486710560)]
theorem point_links_checked24594 : (cuts24594.take 1).map (fun c => (3227516929-1+2*2^9*c.k,102687885827203+c.lower,102688267725565+c.upper)) = pointBounds24594 := by
 decide +kernel
def cuts24595 : List PrefixCut := [⟨25,101683469,101683532⟩,
⟨124,506229162,506229443⟩,
⟨128,522885115,522885406⟩]
theorem checked24595 : checkPrefixCuts (2^48) 3227648001 9 Manual.Count131072.C024595.packed 128 cuts24595 = true := by
 decide +kernel
def pointBounds24595 : List (Nat × Nat × Nat) := [(3227673600,102688508498416,102688890397133),(3227774976,102688913044109,102689294943044)]
theorem point_links_checked24595 : (cuts24595.take 2).map (fun c => (3227648001-1+2*2^9*c.k,102688406814947+c.lower,102688788713601+c.upper)) = pointBounds24595 := by
 decide +kernel
def cuts24596 : List PrefixCut := [⟨95,383516915,383517131⟩,
⟨128,521207003,521207292⟩]
theorem checked24596 : checkPrefixCuts (2^48) 3227779073 9 Manual.Count131072.C024596.packed 128 cuts24596 = true := by
 decide +kernel
def pointBounds24596 : List (Nat × Nat × Nat) := [(3227876352,102689313216977,102689695116138)]
theorem point_links_checked24596 : (cuts24596.take 1).map (fun c => (3227779073-1+2*2^9*c.k,102688929700062+c.lower,102689311599007+c.upper)) = pointBounds24596 := by
 decide +kernel
def cuts24597 : List PrefixCut := [⟨66,270405475,270405629⟩,
⟨128,518918859,518919151⟩]
theorem checked24597 : checkPrefixCuts (2^48) 3227910145 9 Manual.Count131072.C024597.packed 128 cuts24597 = true := by
 decide +kernel
def pointBounds24597 : List (Nat × Nat × Nat) := [(3227977728,102689721312540,102690103211928)]
theorem point_links_checked24597 : (cuts24597.take 1).map (fun c => (3227910145-1+2*2^9*c.k,102689450907065+c.lower,102689832806299+c.upper)) = pointBounds24597 := by
 decide +kernel
def cuts24598 : List PrefixCut := [⟨37,149541641,149541728⟩,
⟨128,523344599,523344899⟩]
theorem checked24598 : checkPrefixCuts (2^48) 3228041217 9 Manual.Count131072.C024598.packed 128 cuts24598 = true := by
 decide +kernel
def pointBounds24598 : List (Nat × Nat × Nat) := [(3228079104,102690119367565,102690501267178)]
theorem point_links_checked24598 : (cuts24598.take 1).map (fun c => (3228041217-1+2*2^9*c.k,102689969825924+c.lower,102690351725450+c.upper)) = pointBounds24598 := by
 decide +kernel
def cuts24599 : List PrefixCut := [⟨8,32261468,32261486⟩,
⟨107,433779140,433779387⟩,
⟨128,521579486,521579780⟩]
theorem checked24599 : checkPrefixCuts (2^48) 3228172289 9 Manual.Count131072.C024599.packed 128 cuts24599 = true := by
 decide +kernel
def pointBounds24599 : List (Nat × Nat × Nat) := [(3228180480,102690525431991,102690907331835),(3228281856,102690926949663,102691308849736)]
theorem point_links_checked24599 : (cuts24599.take 2).map (fun c => (3228172289-1+2*2^9*c.k,102690493170523+c.lower,102690875070349+c.upper)) = pointBounds24599 := by
 decide +kernel
def cuts24600 : List PrefixCut := [⟨78,318412919,318413097⟩,
⟨128,520512096,520512390⟩]
theorem checked24600 : checkPrefixCuts (2^48) 3228303361 9 Manual.Count131072.C024600.packed 128 cuts24600 = true := by
 decide +kernel
def pointBounds24600 : List (Nat × Nat × Nat) := [(3228383232,102691333162928,102691715063226)]
theorem point_links_checked24600 : (cuts24600.take 1).map (fun c => (3228303361-1+2*2^9*c.k,102691014750009+c.lower,102691396650129+c.upper)) = pointBounds24600 := by
 decide +kernel
def cuts24601 : List PrefixCut := [⟨49,201311373,201311484⟩,
⟨128,526506742,526507028⟩]
theorem checked24601 : checkPrefixCuts (2^48) 3228434433 9 Manual.Count131072.C024601.packed 128 cuts24601 = true := by
 decide +kernel
def pointBounds24601 : List (Nat × Nat × Nat) := [(3228484608,102691736573478,102692118474003)]
theorem point_links_checked24601 : (cuts24601.take 1).map (fun c => (3228434433-1+2*2^9*c.k,102691535262105+c.lower,102691917162519+c.upper)) = pointBounds24601 := by
 decide +kernel
def cuts24602 : List PrefixCut := [⟨20,87356735,87356783⟩,
⟨119,494054788,494055062⟩,
⟨128,527793154,527793447⟩]
theorem checked24602 : checkPrefixCuts (2^48) 3228565505 9 Manual.Count131072.C024602.packed 128 cuts24602 = true := by
 decide +kernel
def pointBounds24602 : List (Nat × Nat × Nat) := [(3228585984,102692149125582,102692531026330),(3228687360,102692555823635,102692937724609)]
theorem point_links_checked24602 : (cuts24602.take 2).map (fun c => (3228565505-1+2*2^9*c.k,102692061768847+c.lower,102692443669547+c.upper)) = pointBounds24602 := by
 decide +kernel
def cuts24603 : List PrefixCut := [⟨90,363967647,363967853⟩,
⟨128,521146156,521146447⟩]
theorem checked24603 : checkPrefixCuts (2^48) 3228696577 9 Manual.Count131072.C024603.packed 128 cuts24603 = true := by
 decide +kernel
def pointBounds24603 : List (Nat × Nat × Nat) := [(3228788736,102692953529648,102693335430847)]
theorem point_links_checked24603 : (cuts24603.take 1).map (fun c => (3228696577-1+2*2^9*c.k,102692589562001+c.lower,102692971462994+c.upper)) = pointBounds24603 := by
 decide +kernel
def cuts24604 : List PrefixCut := [⟨61,244176388,244176525⟩,
⟨128,522694023,522694324⟩]
theorem checked24604 : checkPrefixCuts (2^48) 3228827649 9 Manual.Count131072.C024604.packed 128 cuts24604 = true := by
 decide +kernel
def pointBounds24604 : List (Nat × Nat × Nat) := [(3228890112,102693354884545,102693736785966)]
theorem point_links_checked24604 : (cuts24604.take 1).map (fun c => (3228827649-1+2*2^9*c.k,102693110708157+c.lower,102693492609441+c.upper)) = pointBounds24604 := by
 decide +kernel
def cuts24605 : List PrefixCut := [⟨32,134157079,134157154⟩,
⟨128,524852257,524852545⟩]
theorem checked24605 : checkPrefixCuts (2^48) 3228958721 9 Manual.Count131072.C024605.packed 128 cuts24605 = true := by
 decide +kernel
def pointBounds24605 : List (Nat × Nat × Nat) := [(3228991488,102693767559259,102694149460919)]
theorem point_links_checked24605 : (cuts24605.take 1).map (fun c => (3228958721-1+2*2^9*c.k,102693633402180+c.lower,102694015303765+c.upper)) = pointBounds24605 := by
 decide +kernel
def cuts24606 : List PrefixCut := [⟨3,12029246,12029253⟩,
⟨102,414479449,414479684⟩,
⟨128,517334524,517334817⟩]
theorem checked24606 : checkPrefixCuts (2^48) 3229089793 9 Manual.Count131072.C024606.packed 128 cuts24606 = true := by
 decide +kernel
def pointBounds24606 : List (Nat × Nat × Nat) := [(3229092864,102694170283683,102694552185563),(3229194240,102694572733886,102694954635994)]
theorem point_links_checked24606 : (cuts24606.take 2).map (fun c => (3229089793-1+2*2^9*c.k,102694158254437+c.lower,102694540156310+c.upper)) = pointBounds24606 := by
 decide +kernel
def cuts24607 : List PrefixCut := [⟨73,290081655,290081824⟩,
⟨128,511822243,511822535⟩]
theorem checked24607 : checkPrefixCuts (2^48) 3229220865 9 Manual.Count131072.C024607.packed 128 cuts24607 = true := by
 decide +kernel
def pointBounds24607 : List (Nat × Nat × Nat) := [(3229295616,102694965670616,102695347572951)]
theorem point_links_checked24607 : (cuts24607.take 1).map (fun c => (3229220865-1+2*2^9*c.k,102694675588961+c.lower,102695057491127+c.upper)) = pointBounds24607 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000143
