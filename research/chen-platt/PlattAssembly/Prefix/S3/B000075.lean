import PlattAssemblyKernel
import PlattCertificates.Count131072.C022400
import PlattCertificates.Count131072.C022401
import PlattCertificates.Count131072.C022402
import PlattCertificates.Count131072.C022403
import PlattCertificates.Count131072.C022404
import PlattCertificates.Count131072.C022405
import PlattCertificates.Count131072.C022406
import PlattCertificates.Count131072.C022407
import PlattCertificates.Count131072.C022408
import PlattCertificates.Count131072.C022409
import PlattCertificates.Count131072.C022410
import PlattCertificates.Count131072.C022411
import PlattCertificates.Count131072.C022412
import PlattCertificates.Count131072.C022413
import PlattCertificates.Count131072.C022414
import PlattCertificates.Count131072.C022415
import PlattCertificates.Count131072.C022416
import PlattCertificates.Count131072.C022417
import PlattCertificates.Count131072.C022418
import PlattCertificates.Count131072.C022419
import PlattCertificates.Count131072.C022420
import PlattCertificates.Count131072.C022421
import PlattCertificates.Count131072.C022422
import PlattCertificates.Count131072.C022423
import PlattCertificates.Count131072.C022424
import PlattCertificates.Count131072.C022425
import PlattCertificates.Count131072.C022426
import PlattCertificates.Count131072.C022427
import PlattCertificates.Count131072.C022428
import PlattCertificates.Count131072.C022429
import PlattCertificates.Count131072.C022430
import PlattCertificates.Count131072.C022431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22400 : List PrefixCut := [⟨8,35424325,35424344⟩,
⟨98,439637724,439637973⟩,
⟨128,575585381,575585708⟩]
theorem checked22400 : checkPrefixCuts (2^48) 2939944961 9 Manual.Count131072.C022400.packed 128 cuts22400 = true := by
 decide +kernel
def pointBounds22400 : List (Nat × Nat × Nat) := [(2939953152,101485725168592,101486106385897),(2940045312,101486129381991,101486510599526)]
theorem point_links_checked22400 : (cuts22400.take 2).map (fun c => (2939944961-1+2*2^9*c.k,101485689744267+c.lower,101486070961553+c.upper)) = pointBounds22400 := by
 decide +kernel
def cuts22401 : List PrefixCut := [⟨60,273614303,273614457⟩,
⟨128,584941762,584942085⟩]
theorem checked22401 : checkPrefixCuts (2^48) 2940076033 9 Manual.Count131072.C022401.packed 128 cuts22401 = true := by
 decide +kernel
def pointBounds22401 : List (Nat × Nat × Nat) := [(2940137472,101486538943951,101486920161718)]
theorem point_links_checked22401 : (cuts22401.take 1).map (fun c => (2940076033-1+2*2^9*c.k,101486265329648+c.lower,101486646547261+c.upper)) = pointBounds22401 := by
 decide +kernel
def cuts22402 : List PrefixCut := [⟨22,100710750,100710804⟩,
⟨112,508715331,508715618⟩,
⟨128,581086469,581086797⟩]
theorem checked22402 : checkPrefixCuts (2^48) 2940207105 9 Manual.Count131072.C022402.packed 128 cuts22402 = true := by
 decide +kernel
def pointBounds22402 : List (Nat × Nat × Nat) := [(2940229632,101486950982160,101487332200150),(2940321792,101487358986741,101487740204964)]
theorem point_links_checked22402 : (cuts22402.take 2).map (fun c => (2940207105-1+2*2^9*c.k,101486850271410+c.lower,101487231489346+c.upper)) = pointBounds22402 := by
 decide +kernel
def cuts22403 : List PrefixCut := [⟨74,329781314,329781504⟩,
⟨128,572828047,572828378⟩]
theorem checked22403 : checkPrefixCuts (2^48) 2940338177 9 Manual.Count131072.C022403.packed 128 cuts22403 = true := by
 decide +kernel
def pointBounds22403 : List (Nat × Nat × Nat) := [(2940413952,101487761139193,101488142357647)]
theorem point_links_checked22403 : (cuts22403.take 1).map (fun c => (2940338177-1+2*2^9*c.k,101487431357879+c.lower,101487812576143+c.upper)) = pointBounds22403 := by
 decide +kernel
def cuts22404 : List PrefixCut := [⟨36,163496384,163496476⟩,
⟨126,574621451,574621781⟩,
⟨128,583714874,583715210⟩]
theorem checked22404 : checkPrefixCuts (2^48) 2940469249 9 Manual.Count131072.C022404.packed 128 cuts22404 = true := by
 decide +kernel
def pointBounds22404 : List (Nat × Nat × Nat) := [(2940506112,101488167682310,101488548900997),(2940598272,101488578807377,101488960026302)]
theorem point_links_checked22404 : (cuts22404.take 2).map (fun c => (2940469249-1+2*2^9*c.k,101488004185926+c.lower,101488385404521+c.upper)) = pointBounds22404 := by
 decide +kernel
def cuts22405 : List PrefixCut := [⟨88,394935521,394935752⟩,
⟨128,576797076,576797413⟩]
theorem checked22405 : checkPrefixCuts (2^48) 2940600321 9 Manual.Count131072.C022405.packed 128 cuts22405 = true := by
 decide +kernel
def pointBounds22405 : List (Nat × Nat × Nat) := [(2940690432,101488982836321,101489364055483)]
theorem point_links_checked22405 : (cuts22405.take 1).map (fun c => (2940600321-1+2*2^9*c.k,101488587900800+c.lower,101488969119731+c.upper)) = pointBounds22405 := by
 decide +kernel
def cuts22406 : List PrefixCut := [⟨50,227131957,227132088⟩,
⟨128,579738556,579738888⟩]
theorem checked22406 : checkPrefixCuts (2^48) 2940731393 9 Manual.Count131072.C022406.packed 128 cuts22406 = true := by
 decide +kernel
def pointBounds22406 : List (Nat × Nat × Nat) := [(2940782592,101489391829833,101489773049232)]
theorem point_links_checked22406 : (cuts22406.take 1).map (fun c => (2940731393-1+2*2^9*c.k,101489164697876+c.lower,101489545917144+c.upper)) = pointBounds22406 := by
 decide +kernel
def cuts22407 : List PrefixCut := [⟨12,55129814,55129843⟩,
⟨102,461992118,461992379⟩,
⟨128,578947118,578947443⟩]
theorem checked22407 : checkPrefixCuts (2^48) 2940862465 9 Manual.Count131072.C022407.packed 128 cuts22407 = true := by
 decide +kernel
def pointBounds22407 : List (Nat × Nat × Nat) := [(2940874752,101489799566246,101490180785875),(2940966912,101490206428550,101490587648411)]
theorem point_links_checked22407 : (cuts22407.take 2).map (fun c => (2940862465-1+2*2^9*c.k,101489744436432+c.lower,101490125656032+c.upper)) = pointBounds22407 := by
 decide +kernel
def cuts22408 : List PrefixCut := [⟨64,287023362,287023526⟩,
⟨128,575475850,575476176⟩]
theorem checked22408 : checkPrefixCuts (2^48) 2940993537 9 Manual.Count131072.C022408.packed 128 cuts22408 = true := by
 decide +kernel
def pointBounds22408 : List (Nat × Nat × Nat) := [(2941059072,101490610406912,101490991627001)]
theorem point_links_checked22408 : (cuts22408.take 1).map (fun c => (2940993537-1+2*2^9*c.k,101490323383550+c.lower,101490704603475+c.upper)) = pointBounds22408 := by
 decide +kernel
def cuts22409 : List PrefixCut := [⟨26,117905756,117905821⟩,
⟨116,519753345,519753636⟩,
⟨128,573727633,573727955⟩]
theorem checked22409 : checkPrefixCuts (2^48) 2941124609 9 Manual.Count131072.C022409.packed 128 cuts22409 = true := by
 decide +kernel
def pointBounds22409 : List (Nat × Nat × Nat) := [(2941151232,101491016765156,101491397985472),(2941243392,101491418612745,101491799833287)]
theorem point_links_checked22409 : (cuts22409.take 2).map (fun c => (2941124609-1+2*2^9*c.k,101490898859400+c.lower,101491280079651+c.upper)) = pointBounds22409 := by
 decide +kernel
def cuts22410 : List PrefixCut := [⟨78,346999417,346999621⟩,
⟨128,571405245,571405578⟩]
theorem checked22410 : checkPrefixCuts (2^48) 2941255681 9 Manual.Count131072.C022410.packed 128 cuts22410 = true := by
 decide +kernel
def pointBounds22410 : List (Nat × Nat × Nat) := [(2941335552,101491819586450,101492200807227)]
theorem point_links_checked22410 : (cuts22410.take 1).map (fun c => (2941255681-1+2*2^9*c.k,101491472587033+c.lower,101491853807606+c.upper)) = pointBounds22410 := by
 decide +kernel
def cuts22411 : List PrefixCut := [⟨40,180670205,180670315⟩,
⟨128,573389458,573389795⟩]
theorem checked22411 : checkPrefixCuts (2^48) 2941386753 9 Manual.Count131072.C022411.packed 128 cuts22411 = true := by
 decide +kernel
def pointBounds22411 : List (Nat × Nat × Nat) := [(2941427712,101492224662483,101492605883499)]
theorem point_links_checked22411 : (cuts22411.take 1).map (fun c => (2941386753-1+2*2^9*c.k,101492043992278+c.lower,101492425213184+c.upper)) = pointBounds22411 := by
 decide +kernel
def cuts22412 : List PrefixCut := [⟨2,8612129,8612134⟩,
⟨92,415863668,415863911⟩,
⟨128,577382824,577383155⟩]
theorem checked22412 : checkPrefixCuts (2^48) 2941517825 9 Manual.Count131072.C022412.packed 128 cuts22412 = true := by
 decide +kernel
def pointBounds22412 : List (Nat × Nat × Nat) := [(2941519872,101492625993865,101493007215113),(2941612032,101493033245404,101493414466890)]
theorem point_links_checked22412 : (cuts22412.take 2).map (fun c => (2941517825-1+2*2^9*c.k,101492617381736+c.lower,101492998602979+c.upper)) = pointBounds22412 := by
 decide +kernel
def cuts22413 : List PrefixCut := [⟨54,241509449,241509588⟩,
⟨128,570372097,570372427⟩]
theorem checked22413 : checkPrefixCuts (2^48) 2941648897 9 Manual.Count131072.C022413.packed 128 cuts22413 = true := by
 decide +kernel
def pointBounds22413 : List (Nat × Nat × Nat) := [(2941704192,101493436274009,101493817495722)]
theorem point_links_checked22413 : (cuts22413.take 1).map (fun c => (2941648897-1+2*2^9*c.k,101493194764560+c.lower,101493575986134+c.upper)) = pointBounds22413 := by
 decide +kernel
def cuts22414 : List PrefixCut := [⟨16,72430939,72430981⟩,
⟨106,478974400,478974676⟩,
⟨128,577044282,577044617⟩]
theorem checked22414 : checkPrefixCuts (2^48) 2941779969 9 Manual.Count131072.C022414.packed 128 cuts22414 = true := by
 decide +kernel
def pointBounds22414 : List (Nat × Nat × Nat) := [(2941796352,101493837567596,101494218789542),(2941888512,101494244111057,101494625333237)]
theorem point_links_checked22414 : (cuts22414.take 2).map (fun c => (2941779969-1+2*2^9*c.k,101493765136657+c.lower,101494146358561+c.upper)) = pointBounds22414 := by
 decide +kernel
def cuts22415 : List PrefixCut := [⟨68,309417613,309417789⟩,
⟨128,575774851,575775179⟩]
theorem checked22415 : checkPrefixCuts (2^48) 2941911041 9 Manual.Count131072.C022415.packed 128 cuts22415 = true := by
 decide +kernel
def pointBounds22415 : List (Nat × Nat × Nat) := [(2941980672,101494651598552,101495032820967)]
theorem point_links_checked22415 : (cuts22415.take 1).map (fun c => (2941911041-1+2*2^9*c.k,101494342180939+c.lower,101494723403178+c.upper)) = pointBounds22415 := by
 decide +kernel
def cuts22416 : List PrefixCut := [⟨30,129540969,129541044⟩,
⟨120,531071344,531071647⟩,
⟨128,566373271,566373594⟩]
theorem checked22416 : checkPrefixCuts (2^48) 2942042113 9 Manual.Count131072.C022416.packed 128 cuts22416 = true := by
 decide +kernel
def pointBounds22416 : List (Nat × Nat × Nat) := [(2942072832,101495047496759,101495428719401),(2942164992,101495449027134,101495830250004)]
theorem point_links_checked22416 : (cuts22416.take 2).map (fun c => (2942042113-1+2*2^9*c.k,101494917955790+c.lower,101495299178357+c.upper)) = pointBounds22416 := by
 decide +kernel
def cuts22417 : List PrefixCut := [⟨82,368511911,368512128⟩,
⟨128,579454417,579454756⟩]
theorem checked22417 : checkPrefixCuts (2^48) 2942173185 9 Manual.Count131072.C022417.packed 128 cuts22417 = true := by
 decide +kernel
def pointBounds22417 : List (Nat × Nat × Nat) := [(2942257152,101495852840972,101496234064079)]
theorem point_links_checked22417 : (cuts22417.take 1).map (fun c => (2942173185-1+2*2^9*c.k,101495484329061+c.lower,101495865551951+c.upper)) = pointBounds22417 := by
 decide +kernel
def cuts22418 : List PrefixCut := [⟨44,197450594,197450710⟩,
⟨128,571584330,571584665⟩]
theorem checked22418 : checkPrefixCuts (2^48) 2942304257 9 Manual.Count131072.C022418.packed 128 cuts22418 = true := by
 decide +kernel
def pointBounds22418 : List (Nat × Nat × Nat) := [(2942349312,101496261234072,101496642457417)]
theorem point_links_checked22418 : (cuts22418.take 1).map (fun c => (2942304257-1+2*2^9*c.k,101496063783478+c.lower,101496445006707+c.upper)) = pointBounds22418 := by
 decide +kernel
def cuts22419 : List PrefixCut := [⟨6,26689257,26689273⟩,
⟨96,431134695,431134939⟩,
⟨128,572228460,572228787⟩]
theorem checked22419 : checkPrefixCuts (2^48) 2942435329 9 Manual.Count131072.C022419.packed 128 cuts22419 = true := by
 decide +kernel
def pointBounds22419 : List (Nat × Nat × Nat) := [(2942441472,101496662057065,101497043280645),(2942533632,101497066502503,101497447726311)]
theorem point_links_checked22419 : (cuts22419.take 2).map (fun c => (2942435329-1+2*2^9*c.k,101496635367808+c.lower,101497016591372+c.upper)) = pointBounds22419 := by
 decide +kernel
def cuts22420 : List PrefixCut := [⟨58,259130172,259130323⟩,
⟨128,580237843,580238176⟩]
theorem checked22420 : checkPrefixCuts (2^48) 2942566401 9 Manual.Count131072.C022420.packed 128 cuts22420 = true := by
 decide +kernel
def pointBounds22420 : List (Nat × Nat × Nat) := [(2942625792,101497466726440,101497847950482)]
theorem point_links_checked22420 : (cuts22420.take 1).map (fun c => (2942566401-1+2*2^9*c.k,101497207596268+c.lower,101497588820159+c.upper)) = pointBounds22420 := by
 decide +kernel
def cuts22421 : List PrefixCut := [⟨20,91347337,91347390⟩,
⟨110,494798289,494798573⟩,
⟨128,576673007,576673336⟩]
theorem checked22421 : checkPrefixCuts (2^48) 2942697473 9 Manual.Count131072.C022421.packed 128 cuts22421 = true := by
 decide +kernel
def pointBounds22421 : List (Nat × Nat × Nat) := [(2942717952,101497879181448,101498260405725),(2942810112,101498282632400,101498663856908)]
theorem point_links_checked22421 : (cuts22421.take 2).map (fun c => (2942697473-1+2*2^9*c.k,101497787834111+c.lower,101498169058335+c.upper)) = pointBounds22421 := by
 decide +kernel
def cuts22422 : List PrefixCut := [⟨72,322998326,322998515⟩,
⟨128,575308276,575308616⟩]
theorem checked22422 : checkPrefixCuts (2^48) 2942828545 9 Manual.Count131072.C022422.packed 128 cuts22422 = true := by
 decide +kernel
def pointBounds22422 : List (Nat × Nat × Nat) := [(2942902272,101498687505444,101499068730186)]
theorem point_links_checked22422 : (cuts22422.take 1).map (fun c => (2942828545-1+2*2^9*c.k,101498364507118+c.lower,101498745731671+c.upper)) = pointBounds22422 := by
 decide +kernel
def cuts22423 : List PrefixCut := [⟨34,155132809,155132894⟩,
⟨124,554242078,554242394⟩,
⟨128,571648428,571648755⟩]
theorem checked22423 : checkPrefixCuts (2^48) 2942959617 9 Manual.Count131072.C022423.packed 128 cuts22423 = true := by
 decide +kernel
def pointBounds22423 : List (Nat × Nat × Nat) := [(2942994432,101499094948203,101499476173181),(2943086592,101499494057472,101499875282681)]
theorem point_links_checked22423 : (cuts22423.take 2).map (fun c => (2942959617-1+2*2^9*c.k,101498939815394+c.lower,101499321040287+c.upper)) = pointBounds22423 := by
 decide +kernel
def cuts22424 : List PrefixCut := [⟨86,385802867,385803084⟩,
⟨128,577743630,577743955⟩]
theorem checked22424 : checkPrefixCuts (2^48) 2943090689 9 Manual.Count131072.C022424.packed 128 cuts22424 = true := by
 decide +kernel
def pointBounds22424 : List (Nat × Nat × Nat) := [(2943178752,101499897266689,101500278492126)]
theorem point_links_checked22424 : (cuts22424.take 1).map (fun c => (2943090689-1+2*2^9*c.k,101499511463822+c.lower,101499892689042+c.upper)) = pointBounds22424 := by
 decide +kernel
def cuts22425 : List PrefixCut := [⟨48,213646743,213646863⟩,
⟨128,570928024,570928346⟩]
theorem checked22425 : checkPrefixCuts (2^48) 2943221761 9 Manual.Count131072.C022425.packed 128 cuts22425 = true := by
 decide +kernel
def pointBounds22425 : List (Nat × Nat × Nat) := [(2943270912,101500302854195,101500684079860)]
theorem point_links_checked22425 : (cuts22425.take 1).map (fun c => (2943221761-1+2*2^9*c.k,101500089207452+c.lower,101500470432997+c.upper)) = pointBounds22425 := by
 decide +kernel
def cuts22426 : List PrefixCut := [⟨10,45041982,45042011⟩,
⟨100,449743429,449743696⟩,
⟨128,575397192,575397532⟩]
theorem checked22426 : checkPrefixCuts (2^48) 2943352833 9 Manual.Count131072.C022426.packed 128 cuts22426 = true := by
 decide +kernel
def pointBounds22426 : List (Nat × Nat × Nat) := [(2943363072,101500705177458,101501086403354),(2943455232,101501109878905,101501491105039)]
theorem point_links_checked22426 : (cuts22426.take 2).map (fun c => (2943352833-1+2*2^9*c.k,101500660135476+c.lower,101501041361343+c.upper)) = pointBounds22426 := by
 decide +kernel
def cuts22427 : List PrefixCut := [⟨62,277313661,277313826⟩,
⟨128,575945177,575945509⟩]
theorem checked22427 : checkPrefixCuts (2^48) 2943483905 9 Manual.Count131072.C022427.packed 128 cuts22427 = true := by
 decide +kernel
def pointBounds22427 : List (Nat × Nat × Nat) := [(2943547392,101501512846329,101501894072701)]
theorem point_links_checked22427 : (cuts22427.take 1).map (fun c => (2943483905-1+2*2^9*c.k,101501235532668+c.lower,101501616758875+c.upper)) = pointBounds22427 := by
 decide +kernel
def cuts22428 : List PrefixCut := [⟨24,111781857,111781920⟩,
⟨114,511951087,511951381⟩,
⟨128,573146711,573147042⟩]
theorem checked22428 : checkPrefixCuts (2^48) 2943614977 9 Manual.Count131072.C022428.packed 128 cuts22428 = true := by
 decide +kernel
def pointBounds22428 : List (Nat × Nat × Nat) := [(2943639552,101501923259702,101502304486304),(2943731712,101502323428932,101502704655765)]
theorem point_links_checked22428 : (cuts22428.take 2).map (fun c => (2943614977-1+2*2^9*c.k,101501811477845+c.lower,101502192704384+c.upper)) = pointBounds22428 := by
 decide +kernel
def cuts22429 : List PrefixCut := [⟨76,336953120,336953318⟩,
⟨128,572738521,572738851⟩]
theorem checked22429 : checkPrefixCuts (2^48) 2943746049 9 Manual.Count131072.C022429.packed 128 cuts22429 = true := by
 decide +kernel
def pointBounds22429 : List (Nat × Nat × Nat) := [(2943823872,101502721577676,101503102804744)]
theorem point_links_checked22429 : (cuts22429.take 1).map (fun c => (2943746049-1+2*2^9*c.k,101502384624556+c.lower,101502765851426+c.upper)) = pointBounds22429 := by
 decide +kernel
def cuts22430 : List PrefixCut := [⟨38,170573648,170573745⟩,
⟨128,576059522,576059852⟩]
theorem checked22430 : checkPrefixCuts (2^48) 2943877121 9 Manual.Count131072.C022430.packed 128 cuts22430 = true := by
 decide +kernel
def pointBounds22430 : List (Nat × Nat × Nat) := [(2943916032,101503127936725,101503509164022),(2944008192,101503533422599,101503914650129)]
theorem point_links_checked22430 : (cuts22430.take 2).map (fun c => (2943877121-1+2*2^9*c.k,101502957363077+c.lower,101503338590277+c.upper)) = pointBounds22430 := by
 decide +kernel
def cuts22431 : List PrefixCut := [⟨90,407098518,407098753⟩,
⟨128,577372429,577372763⟩]
theorem checked22431 : checkPrefixCuts (2^48) 2944008193 9 Manual.Count131072.C022431.packed 128 cuts22431 = true := by
 decide +kernel
def pointBounds22431 : List (Nat × Nat × Nat) := [(2944100352,101503940521117,101504321748882)]
theorem point_links_checked22431 : (cuts22431.take 1).map (fun c => (2944008193-1+2*2^9*c.k,101503533422599+c.lower,101503914650129+c.upper)) = pointBounds22431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000075
