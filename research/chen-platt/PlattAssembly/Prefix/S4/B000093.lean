import PlattAssemblyKernel
import PlattCertificates.Count131072.C032976
import PlattCertificates.Count131072.C032977
import PlattCertificates.Count131072.C032978
import PlattCertificates.Count131072.C032979
import PlattCertificates.Count131072.C032980
import PlattCertificates.Count131072.C032981
import PlattCertificates.Count131072.C032982
import PlattCertificates.Count131072.C032983
import PlattCertificates.Count131072.C032984
import PlattCertificates.Count131072.C032985
import PlattCertificates.Count131072.C032986
import PlattCertificates.Count131072.C032987
import PlattCertificates.Count131072.C032988
import PlattCertificates.Count131072.C032989
import PlattCertificates.Count131072.C032990
import PlattCertificates.Count131072.C032991
import PlattCertificates.Count131072.C032992
import PlattCertificates.Count131072.C032993
import PlattCertificates.Count131072.C032994
import PlattCertificates.Count131072.C032995
import PlattCertificates.Count131072.C032996
import PlattCertificates.Count131072.C032997
import PlattCertificates.Count131072.C032998
import PlattCertificates.Count131072.C032999
import PlattCertificates.Count131072.C033000
import PlattCertificates.Count131072.C033001
import PlattCertificates.Count131072.C033002
import PlattCertificates.Count131072.C033003
import PlattCertificates.Count131072.C033004
import PlattCertificates.Count131072.C033005
import PlattCertificates.Count131072.C033006
import PlattCertificates.Count131072.C033007
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32976 : List PrefixCut := [⟨9,53482012,53482047⟩,
⟨64,389398564,389398811⟩]
theorem checked32976 : checkPrefixCuts (2^48) 4326162433 10 Manual.Count131072.C032976.packed 64 cuts32976 = true := by
 decide +kernel
def pointBounds32976 : List (Nat × Nat × Nat) := [(4326180864,106429232042211,106429616048828)]
theorem point_links_checked32976 : (cuts32976.take 1).map (fun c => (4326162433-1+2*2^10*c.k,106429178560199+c.lower,106429562566781+c.upper)) = pointBounds32976 := by
 decide +kernel
def cuts32977 : List PrefixCut := [⟨12,74039710,74039757⟩,
⟨64,388541057,388541308⟩]
theorem checked32977 : checkPrefixCuts (2^48) 4326293505 10 Manual.Count131072.C032977.packed 64 cuts32977 = true := by
 decide +kernel
def pointBounds32977 : List (Nat × Nat × Nat) := [(4326318080,106429641998473,106430026005349)]
theorem point_links_checked32977 : (cuts32977.take 1).map (fun c => (4326293505-1+2*2^10*c.k,106429567958763+c.lower,106429951965592+c.upper)) = pointBounds32977 := by
 decide +kernel
def cuts32978 : List PrefixCut := [⟨15,90367277,90367336⟩,
⟨64,382934210,382934456⟩]
theorem checked32978 : checkPrefixCuts (2^48) 4326424577 10 Manual.Count131072.C032978.packed 64 cuts32978 = true := by
 decide +kernel
def pointBounds32978 : List (Nat × Nat × Nat) := [(4326455296,106430046867097,106430430874236)]
theorem point_links_checked32978 : (cuts32978.take 1).map (fun c => (4326424577-1+2*2^10*c.k,106429956499820+c.lower,106430340506900+c.upper)) = pointBounds32978 := by
 decide +kernel
def cuts32979 : List PrefixCut := [⟨18,111312912,111312981⟩,
⟨64,390729427,390729670⟩]
theorem checked32979 : checkPrefixCuts (2^48) 4326555649 10 Manual.Count131072.C032979.packed 64 cuts32979 = true := by
 decide +kernel
def pointBounds32979 : List (Nat × Nat × Nat) := [(4326592512,106430450746942,106430834754337)]
theorem point_links_checked32979 : (cuts32979.take 1).map (fun c => (4326555649-1+2*2^10*c.k,106430339434030+c.lower,106430723441356+c.upper)) = pointBounds32979 := by
 decide +kernel
def cuts32980 : List PrefixCut := [⟨21,125751706,125751786⟩,
⟨64,385968582,385968827⟩]
theorem checked32980 : checkPrefixCuts (2^48) 4326686721 10 Manual.Count131072.C032980.packed 64 cuts32980 = true := by
 decide +kernel
def pointBounds32980 : List (Nat × Nat × Nat) := [(4326729728,106430855915163,106431239922812)]
theorem point_links_checked32980 : (cuts32980.take 1).map (fun c => (4326686721-1+2*2^10*c.k,106430730163457+c.lower,106431114171026+c.upper)) = pointBounds32980 := by
 decide +kernel
def cuts32981 : List PrefixCut := [⟨24,142271311,142271404⟩,
⟨64,379191413,379191659⟩]
theorem checked32981 : checkPrefixCuts (2^48) 4326817793 10 Manual.Count131072.C032981.packed 64 cuts32981 = true := by
 decide +kernel
def pointBounds32981 : List (Nat × Nat × Nat) := [(4326866944,106431258403350,106431642411257)]
theorem point_links_checked32981 : (cuts32981.take 1).map (fun c => (4326817793-1+2*2^10*c.k,106431116132039+c.lower,106431500139853+c.upper)) = pointBounds32981 := by
 decide +kernel
def cuts32982 : List PrefixCut := [⟨27,163603704,163603806⟩,
⟨64,385164621,385164864⟩]
theorem checked32982 : checkPrefixCuts (2^48) 4326948865 10 Manual.Count131072.C032982.packed 64 cuts32982 = true := by
 decide +kernel
def pointBounds32982 : List (Nat × Nat × Nat) := [(4327004160,106431658927156,106432042935318)]
theorem point_links_checked32982 : (cuts32982.take 1).map (fun c => (4326948865-1+2*2^10*c.k,106431495323452+c.lower,106431879331512+c.upper)) = pointBounds32982 := by
 decide +kernel
def cuts32983 : List PrefixCut := [⟨30,180576448,180576564⟩,
⟨64,382290819,382291065⟩]
theorem checked32983 : checkPrefixCuts (2^48) 4327079937 10 Manual.Count131072.C032983.packed 64 cuts32983 = true := by
 decide +kernel
def pointBounds32983 : List (Nat × Nat × Nat) := [(4327141376,106432061064521,106432445072940)]
theorem point_links_checked32983 : (cuts32983.take 1).map (fun c => (4327079937-1+2*2^10*c.k,106431880488073+c.lower,106432264496376+c.upper)) = pointBounds32983 := by
 decide +kernel
def cuts32984 : List PrefixCut := [⟨33,195987018,195987146⟩,
⟨64,381823880,381824129⟩]
theorem checked32984 : checkPrefixCuts (2^48) 4327211009 10 Manual.Count131072.C032984.packed 64 cuts32984 = true := by
 decide +kernel
def pointBounds32984 : List (Nat × Nat × Nat) := [(4327278592,106432458765910,106432842774587)]
theorem point_links_checked32984 : (cuts32984.take 1).map (fun c => (4327211009-1+2*2^10*c.k,106432262778892+c.lower,106432646787441+c.upper)) = pointBounds32984 := by
 decide +kernel
def cuts32985 : List PrefixCut := [⟨36,212892669,212892805⟩,
⟨64,380381332,380381573⟩]
theorem checked32985 : checkPrefixCuts (2^48) 4327342081 10 Manual.Count131072.C032985.packed 64 cuts32985 = true := by
 decide +kernel
def pointBounds32985 : List (Nat × Nat × Nat) := [(4327415808,106432857495441,106433241504375)]
theorem point_links_checked32985 : (cuts32985.take 1).map (fun c => (4327342081-1+2*2^10*c.k,106432644602772+c.lower,106433028611570+c.upper)) = pointBounds32985 := by
 decide +kernel
def cuts32986 : List PrefixCut := [⟨39,233179549,233179697⟩,
⟨64,380304828,380305072⟩]
theorem checked32986 : checkPrefixCuts (2^48) 4327473153 10 Manual.Count131072.C032986.packed 64 cuts32986 = true := by
 decide +kernel
def pointBounds32986 : List (Nat × Nat × Nat) := [(4327553024,106433258163653,106433642172840)]
theorem point_links_checked32986 : (cuts32986.take 1).map (fun c => (4327473153-1+2*2^10*c.k,106433024984104+c.lower,106433408993143+c.upper)) = pointBounds32986 := by
 decide +kernel
def cuts32987 : List PrefixCut := [⟨42,253009857,253010021⟩,
⟨64,385756712,385756958⟩]
theorem checked32987 : checkPrefixCuts (2^48) 4327604225 10 Manual.Count131072.C032987.packed 64 cuts32987 = true := by
 decide +kernel
def pointBounds32987 : List (Nat × Nat × Nat) := [(4327690240,106433658298789,106434042308236)]
theorem point_links_checked32987 : (cuts32987.take 1).map (fun c => (4327604225-1+2*2^10*c.k,106433405288932+c.lower,106433789298215+c.upper)) = pointBounds32987 := by
 decide +kernel
def cuts32988 : List PrefixCut := [⟨45,270432452,270432621⟩,
⟨64,381322388,381322631⟩]
theorem checked32988 : checkPrefixCuts (2^48) 4327735297 10 Manual.Count131072.C032988.packed 64 cuts32988 = true := by
 decide +kernel
def pointBounds32988 : List (Nat × Nat × Nat) := [(4327827456,106434061478096,106434445487794)]
theorem point_links_checked32988 : (cuts32988.take 1).map (fun c => (4327735297-1+2*2^10*c.k,106433791045644+c.lower,106434175055173+c.upper)) = pointBounds32988 := by
 decide +kernel
def cuts32989 : List PrefixCut := [⟨48,292276537,292276721⟩,
⟨64,387749499,387749742⟩]
theorem checked32989 : checkPrefixCuts (2^48) 4327866369 10 Manual.Count131072.C032989.packed 64 cuts32989 = true := by
 decide +kernel
def pointBounds32989 : List (Nat × Nat × Nat) := [(4327964672,106434464644569,106434848654525)]
theorem point_links_checked32989 : (cuts32989.take 1).map (fun c => (4327866369-1+2*2^10*c.k,106434172368032+c.lower,106434556377804+c.upper)) = pointBounds32989 := by
 decide +kernel
def cuts32990 : List PrefixCut := [⟨51,308851337,308851540⟩,
⟨64,387152336,387152591⟩]
theorem checked32990 : checkPrefixCuts (2^48) 4327997441 10 Manual.Count131072.C032990.packed 64 cuts32990 = true := by
 decide +kernel
def pointBounds32990 : List (Nat × Nat × Nat) := [(4328101888,106434868968868,106435252979086)]
theorem point_links_checked32990 : (cuts32990.take 1).map (fun c => (4327997441-1+2*2^10*c.k,106434560117531+c.lower,106434944127546+c.upper)) = pointBounds32990 := by
 decide +kernel
def cuts32991 : List PrefixCut := [⟨54,321783431,321783636⟩,
⟨64,382718453,382718698⟩]
theorem checked32991 : checkPrefixCuts (2^48) 4328128513 10 Manual.Count131072.C032991.packed 64 cuts32991 = true := by
 decide +kernel
def pointBounds32991 : List (Nat × Nat × Nat) := [(4328239104,106435269053298,106435653063773)]
theorem point_links_checked32991 : (cuts32991.take 1).map (fun c => (4328128513-1+2*2^10*c.k,106434947269867+c.lower,106435331280137+c.upper)) = pointBounds32991 := by
 decide +kernel
def cuts32992 : List PrefixCut := [⟨57,339656982,339657202⟩,
⟨64,381731407,381731656⟩]
theorem checked32992 : checkPrefixCuts (2^48) 4328259585 10 Manual.Count131072.C032992.packed 64 cuts32992 = true := by
 decide +kernel
def pointBounds32992 : List (Nat × Nat × Nat) := [(4328376320,106435669645302,106436053656037)]
theorem point_links_checked32992 : (cuts32992.take 1).map (fun c => (4328259585-1+2*2^10*c.k,106435329988320+c.lower,106435713998835+c.upper)) = pointBounds32992 := by
 decide +kernel
def cuts32993 : List PrefixCut := [⟨60,354342989,354343218⟩,
⟨64,377623016,377623260⟩]
theorem checked32993 : checkPrefixCuts (2^48) 4328390657 10 Manual.Count131072.C032993.packed 64 cuts32993 = true := by
 decide +kernel
def pointBounds32993 : List (Nat × Nat × Nat) := [(4328513536,106436066062716,106436450073709)]
theorem point_links_checked32993 : (cuts32993.take 1).map (fun c => (4328390657-1+2*2^10*c.k,106435711719727+c.lower,106436095730491+c.upper)) = pointBounds32993 := by
 decide +kernel
def cuts32994 : List PrefixCut := [⟨63,377611660,377611894⟩,
⟨64,383984207,383984446⟩]
theorem checked32994 : checkPrefixCuts (2^48) 4328521729 10 Manual.Count131072.C032994.packed 64 cuts32994 = true := by
 decide +kernel
def pointBounds32994 : List (Nat × Nat × Nat) := [(4328650752,106436466954403,106436850965645)]
theorem point_links_checked32994 : (cuts32994.take 1).map (fun c => (4328521729-1+2*2^10*c.k,106436089342743+c.lower,106436473353751+c.upper)) = pointBounds32994 := by
 decide +kernel
def cuts32995 : List PrefixCut := [⟨64,385728308,385728555⟩]
theorem checked32995 : checkPrefixCuts (2^48) 4328652801 10 Manual.Count131072.C032995.packed 64 cuts32995 = true := by
 decide +kernel
def cuts32996 : List PrefixCut := [⟨2,12094461,12094468⟩,
⟨64,387277155,387277402⟩]
theorem checked32996 : checkPrefixCuts (2^48) 4328783873 10 Manual.Count131072.C032996.packed 64 cuts32996 = true := by
 decide +kernel
def pointBounds32996 : List (Nat × Nat × Nat) := [(4328787968,106436871149719,106437255161220)]
theorem point_links_checked32996 : (cuts32996.take 1).map (fun c => (4328783873-1+2*2^10*c.k,106436859055258+c.lower,106437243066752+c.upper)) = pointBounds32996 := by
 decide +kernel
def cuts32997 : List PrefixCut := [⟨5,28999797,28999815⟩,
⟨64,383754301,383754545⟩]
theorem checked32997 : checkPrefixCuts (2^48) 4328914945 10 Manual.Count131072.C032997.packed 64 cuts32997 = true := by
 decide +kernel
def pointBounds32997 : List (Nat × Nat × Nat) := [(4328925184,106437275332210,106437659343969)]
theorem point_links_checked32997 : (cuts32997.take 1).map (fun c => (4328914945-1+2*2^10*c.k,106437246332413+c.lower,106437630344154+c.upper)) = pointBounds32997 := by
 decide +kernel
def cuts32998 : List PrefixCut := [⟨8,50130380,50130411⟩,
⟨64,388033903,388034151⟩]
theorem checked32998 : checkPrefixCuts (2^48) 4329046017 10 Manual.Count131072.C032998.packed 64 cuts32998 = true := by
 decide +kernel
def pointBounds32998 : List (Nat × Nat × Nat) := [(4329062400,106437680217094,106438064229110)]
theorem point_links_checked32998 : (cuts32998.take 1).map (fun c => (4329046017-1+2*2^10*c.k,106437630086714+c.lower,106438014098699+c.upper)) = pointBounds32998 := by
 decide +kernel
def cuts32999 : List PrefixCut := [⟨11,65733130,65733173⟩,
⟨64,384446225,384446473⟩]
theorem checked32999 : checkPrefixCuts (2^48) 4329177089 10 Manual.Count131072.C032999.packed 64 cuts32999 = true := by
 decide +kernel
def pointBounds32999 : List (Nat × Nat × Nat) := [(4329199616,106438083853747,106438467866023)]
theorem point_links_checked32999 : (cuts32999.take 1).map (fun c => (4329177089-1+2*2^10*c.k,106438018120617+c.lower,106438402132850+c.upper)) = pointBounds32999 := by
 decide +kernel
def cuts33000 : List PrefixCut := [⟨14,84325652,84325706⟩,
⟨64,382484104,382484350⟩]
theorem checked33000 : checkPrefixCuts (2^48) 4329308161 10 Manual.Count131072.C033000.packed 64 cuts33000 = true := by
 decide +kernel
def pointBounds33000 : List (Nat × Nat × Nat) := [(4329336832,106438486892494,106438870905029)]
theorem point_links_checked33000 : (cuts33000.take 1).map (fun c => (4329308161-1+2*2^10*c.k,106438402566842+c.lower,106438786579323+c.upper)) = pointBounds33000 := by
 decide +kernel
def cuts33001 : List PrefixCut := [⟨17,103242085,103242149⟩,
⟨64,385203131,385203380⟩]
theorem checked33001 : checkPrefixCuts (2^48) 4329439233 10 Manual.Count131072.C033001.packed 64 cuts33001 = true := by
 decide +kernel
def pointBounds33001 : List (Nat × Nat × Nat) := [(4329474048,106438888293031,106439272305822)]
theorem point_links_checked33001 : (cuts33001.take 1).map (fun c => (4329439233-1+2*2^10*c.k,106438785050946+c.lower,106439169063673+c.upper)) = pointBounds33001 := by
 decide +kernel
def cuts33002 : List PrefixCut := [⟨20,122612433,122612511⟩,
⟨64,389417193,389417440⟩]
theorem checked33002 : checkPrefixCuts (2^48) 4329570305 10 Manual.Count131072.C033002.packed 64 cuts33002 = true := by
 decide +kernel
def pointBounds33002 : List (Nat × Nat × Nat) := [(4329611264,106439292866510,106439676879564)]
theorem point_links_checked33002 : (cuts33002.take 1).map (fun c => (4329570305-1+2*2^10*c.k,106439170254077+c.lower,106439554267053+c.upper)) = pointBounds33002 := by
 decide +kernel
def cuts33003 : List PrefixCut := [⟨23,135415589,135415672⟩,
⟨64,382644418,382644660⟩]
theorem checked33003 : checkPrefixCuts (2^48) 4329701377 10 Manual.Count131072.C033003.packed 64 cuts33003 = true := by
 decide +kernel
def pointBounds33003 : List (Nat × Nat × Nat) := [(4329748480,106439695086859,106440079100165)]
theorem point_links_checked33003 : (cuts33003.take 1).map (fun c => (4329701377-1+2*2^10*c.k,106439559671270+c.lower,106439943684493+c.upper)) = pointBounds33003 := by
 decide +kernel
def cuts33004 : List PrefixCut := [⟨26,159399279,159399383⟩,
⟨64,387898450,387898700⟩]
theorem checked33004 : checkPrefixCuts (2^48) 4329832449 10 Manual.Count131072.C033004.packed 64 cuts33004 = true := by
 decide +kernel
def pointBounds33004 : List (Nat × Nat × Nat) := [(4329885696,106440101714967,106440485728536)]
theorem point_links_checked33004 : (cuts33004.take 1).map (fun c => (4329832449-1+2*2^10*c.k,106439942315688+c.lower,106440326329153+c.upper)) = pointBounds33004 := by
 decide +kernel
def cuts33005 : List PrefixCut := [⟨29,176685897,176686007⟩,
⟨64,388796757,388796999⟩]
theorem checked33005 : checkPrefixCuts (2^48) 4329963521 10 Manual.Count131072.C033005.packed 64 cuts33005 = true := by
 decide +kernel
def pointBounds33005 : List (Nat × Nat × Nat) := [(4330022912,106440506900035,106440890913860)]
theorem point_links_checked33005 : (cuts33005.take 1).map (fun c => (4329963521-1+2*2^10*c.k,106440330214138+c.lower,106440714227853+c.upper)) = pointBounds33005 := by
 decide +kernel
def cuts33006 : List PrefixCut := [⟨32,192541371,192541494⟩,
⟨64,385924843,385925093⟩]
theorem checked33006 : checkPrefixCuts (2^48) 4330094593 10 Manual.Count131072.C033006.packed 64 cuts33006 = true := by
 decide +kernel
def pointBounds33006 : List (Nat × Nat × Nat) := [(4330160128,106440911552266,106441295566346)]
theorem point_links_checked33006 : (cuts33006.take 1).map (fun c => (4330094593-1+2*2^10*c.k,106440719010895+c.lower,106441103024852+c.upper)) = pointBounds33006 := by
 decide +kernel
def cuts33007 : List PrefixCut := [⟨35,208460856,208460988⟩,
⟨64,383768125,383768368⟩]
theorem checked33007 : checkPrefixCuts (2^48) 4330225665 10 Manual.Count131072.C033007.packed 64 cuts33007 = true := by
 decide +kernel
def pointBounds33007 : List (Nat × Nat × Nat) := [(4330297344,106441313396594,106441697410933)]
theorem point_links_checked33007 : (cuts33007.take 1).map (fun c => (4330225665-1+2*2^10*c.k,106441104935738+c.lower,106441488949945+c.upper)) = pointBounds33007 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000093
