import PlattAssemblyKernel
import PlattCertificates.Count131072.C019984
import PlattCertificates.Count131072.C019985
import PlattCertificates.Count131072.C019986
import PlattCertificates.Count131072.C019987
import PlattCertificates.Count131072.C019988
import PlattCertificates.Count131072.C019989
import PlattCertificates.Count131072.C019990
import PlattCertificates.Count131072.C019991
import PlattCertificates.Count131072.C019992
import PlattCertificates.Count131072.C019993
import PlattCertificates.Count131072.C019994
import PlattCertificates.Count131072.C019995
import PlattCertificates.Count131072.C019996
import PlattCertificates.Count131072.C019997
import PlattCertificates.Count131072.C019998
import PlattCertificates.Count131072.C019999
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000312
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19984 : List PrefixCut := [⟨35,176613016,176613120⟩,
⟨116,587878156,587878496⟩,
⟨128,647426288,647426664⟩]
theorem checked19984 : checkPrefixCuts (2^48) 2623275009 9 Manual.Count131072.C019984.packed 128 cuts19984 = true := by
 decide +kernel
def pointBounds19984 : List (Nat × Nat × Nat) := [(2623310848,100010685951211,100011066314992),(2623393792,100011097216351,100011477580368)]
theorem point_links_checked19984 : (cuts19984.take 2).map (fun c => (2623275009-1+2*2^9*c.k,100010509338195+c.lower,100010889701872+c.upper)) = pointBounds19984 := by
 decide +kernel
def cuts19985 : List PrefixCut := [⟨69,348485169,348485372⟩,
⟨128,642780384,642780755⟩]
theorem checked19985 : checkPrefixCuts (2^48) 2623406081 9 Manual.Count131072.C019985.packed 128 cuts19985 = true := by
 decide +kernel
def pointBounds19985 : List (Nat × Nat × Nat) := [(2623476736,100011505249652,100011885613908)]
theorem point_links_checked19985 : (cuts19985.take 1).map (fun c => (2623406081-1+2*2^9*c.k,100011156764483+c.lower,100011537128536+c.upper)) = pointBounds19985 := by
 decide +kernel
def cuts19986 : List PrefixCut := [⟨22,109862753,109862819⟩,
⟨103,517011869,517012176⟩,
⟨128,641675285,641675664⟩]
theorem checked19986 : checkPrefixCuts (2^48) 2623537153 9 Manual.Count131072.C019986.packed 128 cuts19986 = true := by
 decide +kernel
def pointBounds19986 : List (Nat × Nat × Nat) := [(2623559680,100011909407620,100012289772110),(2623642624,100012316556736,100012696921467)]
theorem point_links_checked19986 : (cuts19986.take 2).map (fun c => (2623537153-1+2*2^9*c.k,100011799544867+c.lower,100012179909291+c.upper)) = pointBounds19986 := by
 decide +kernel
def cuts19987 : List PrefixCut := [⟨56,285798686,285798856⟩,
⟨128,654517052,654517440⟩]
theorem checked19987 : checkPrefixCuts (2^48) 2623668225 9 Manual.Count131072.C019987.packed 128 cuts19987 = true := by
 decide +kernel
def pointBounds19987 : List (Nat × Nat × Nat) := [(2623725568,100012727018838,100013107383811)]
theorem point_links_checked19987 : (cuts19987.take 1).map (fun c => (2623668225-1+2*2^9*c.k,100012441220152+c.lower,100012821584955+c.upper)) = pointBounds19987 := by
 decide +kernel
def cuts19988 : List PrefixCut := [⟨9,45485620,45485646⟩,
⟨90,451416157,451416425⟩,
⟨128,641825776,641826153⟩]
theorem checked19988 : checkPrefixCuts (2^48) 2623799297 9 Manual.Count131072.C019988.packed 128 cuts19988 = true := by
 decide +kernel
def pointBounds19988 : List (Nat × Nat × Nat) := [(2623808512,100013141222824,100013521588041),(2623891456,100013547153361,100013927518820)]
theorem point_links_checked19988 : (cuts19988.take 2).map (fun c => (2623799297-1+2*2^9*c.k,100013095737204+c.lower,100013476102395+c.upper)) = pointBounds19988 := by
 decide +kernel
def cuts19989 : List PrefixCut := [⟨43,218940800,218940929⟩,
⟨124,635143525,635143901⟩,
⟨128,656167850,656168238⟩]
theorem checked19989 : checkPrefixCuts (2^48) 2623930369 9 Manual.Count131072.C019989.packed 128 cuts19989 = true := by
 decide +kernel
def pointBounds19989 : List (Nat × Nat × Nat) := [(2623974400,100013956503780,100014336869477),(2624057344,100014372706505,100014753072449)]
theorem point_links_checked19989 : (cuts19989.take 2).map (fun c => (2623930369-1+2*2^9*c.k,100013737562980+c.lower,100014117928548+c.upper)) = pointBounds19989 := by
 decide +kernel
def cuts19990 : List PrefixCut := [⟨77,391947286,391947519⟩,
⟨128,649806549,649806934⟩]
theorem checked19990 : checkPrefixCuts (2^48) 2624061441 9 Manual.Count131072.C019990.packed 128 cuts19990 = true := by
 decide +kernel
def pointBounds19990 : List (Nat × Nat × Nat) := [(2624140288,100014785678116,100015166044305)]
theorem point_links_checked19990 : (cuts19990.take 1).map (fun c => (2624061441-1+2*2^9*c.k,100014393730830+c.lower,100014774096786+c.upper)) = pointBounds19990 := by
 decide +kernel
def cuts19991 : List PrefixCut := [⟨30,153168556,153168650⟩,
⟨111,563325341,563325672⟩,
⟨128,648272502,648272884⟩]
theorem checked19991 : checkPrefixCuts (2^48) 2624192513 9 Manual.Count131072.C019991.packed 128 cuts19991 = true := by
 decide +kernel
def pointBounds19991 : List (Nat × Nat × Nat) := [(2624223232,100015196705935,100015577072370),(2624306176,100015606862720,100015987229392)]
theorem point_links_checked19991 : (cuts19991.take 2).map (fun c => (2624192513-1+2*2^9*c.k,100015043537379+c.lower,100015423903720+c.upper)) = pointBounds19991 := by
 decide +kernel
def cuts19992 : List PrefixCut := [⟨64,320262940,320263134⟩,
⟨128,644164459,644164842⟩]
theorem checked19992 : checkPrefixCuts (2^48) 2624323585 9 Manual.Count131072.C019992.packed 128 cuts19992 = true := by
 decide +kernel
def pointBounds19992 : List (Nat × Nat × Nat) := [(2624389120,100016012072821,100016392439738)]
theorem point_links_checked19992 : (cuts19992.take 1).map (fun c => (2624323585-1+2*2^9*c.k,100015691809881+c.lower,100016072176604+c.upper)) = pointBounds19992 := by
 decide +kernel
def cuts19993 : List PrefixCut := [⟨17,84406116,84406166⟩,
⟨98,496132777,496133063⟩,
⟨128,647885982,647886359⟩]
theorem checked19993 : checkPrefixCuts (2^48) 2624454657 9 Manual.Count131072.C019993.packed 128 cuts19993 = true := by
 decide +kernel
def pointBounds19993 : List (Nat × Nat × Nat) := [(2624472064,100016420380456,100016800747612),(2624555008,100016832107117,100017212474509)]
theorem point_links_checked19993 : (cuts19993.take 2).map (fun c => (2624454657-1+2*2^9*c.k,100016335974340+c.lower,100016716341446+c.upper)) = pointBounds19993 := by
 decide +kernel
def cuts19994 : List PrefixCut := [⟨51,262856015,262856167⟩,
⟨128,654181050,654181435⟩]
theorem checked19994 : checkPrefixCuts (2^48) 2624585729 9 Manual.Count131072.C019994.packed 128 cuts19994 = true := by
 decide +kernel
def pointBounds19994 : List (Nat × Nat × Nat) := [(2624637952,100017246716337,100017627083972)]
theorem point_links_checked19994 : (cuts19994.take 1).map (fun c => (2624585729-1+2*2^9*c.k,100016983860322+c.lower,100017364227805+c.upper)) = pointBounds19994 := by
 decide +kernel
def cuts19995 : List PrefixCut := [⟨4,19839404,19839416⟩,
⟨85,428738752,428739003⟩,
⟨128,651038250,651038628⟩]
theorem checked19995 : checkPrefixCuts (2^48) 2624716801 9 Manual.Count131072.C019995.packed 128 cuts19995 = true := by
 decide +kernel
def pointBounds19995 : List (Nat × Nat × Nat) := [(2624720896,100017657880776,100018038248656),(2624803840,100018066780124,100018447148243)]
theorem point_links_checked19995 : (cuts19995.take 2).map (fun c => (2624716801-1+2*2^9*c.k,100017638041372+c.lower,100018018409240+c.upper)) = pointBounds19995 := by
 decide +kernel
def cuts19996 : List PrefixCut := [⟨38,190769199,190769311⟩,
⟨119,602109071,602109429⟩,
⟨128,645858742,645859124⟩]
theorem checked19996 : checkPrefixCuts (2^48) 2624847873 9 Manual.Count131072.C019996.packed 128 cuts19996 = true := by
 decide +kernel
def pointBounds19996 : List (Nat × Nat × Nat) := [(2624886784,100018479848821,100018860217179),(2624969728,100018891188693,100019271557297)]
theorem point_links_checked19996 : (cuts19996.take 2).map (fun c => (2624847873-1+2*2^9*c.k,100018289079622+c.lower,100018669447868+c.upper)) = pointBounds19996 := by
 decide +kernel
def cuts19997 : List PrefixCut := [⟨72,364467579,364467789⟩,
⟨128,643360315,643360688⟩]
theorem checked19997 : checkPrefixCuts (2^48) 2624978945 9 Manual.Count131072.C019997.packed 128 cuts19997 = true := by
 decide +kernel
def pointBounds19997 : List (Nat × Nat × Nat) := [(2625052672,100019299405943,100019679774781)]
theorem point_links_checked19997 : (cuts19997.take 1).map (fun c => (2624978945-1+2*2^9*c.k,100018934938364+c.lower,100019315306992+c.upper)) = pointBounds19997 := by
 decide +kernel
def cuts19998 : List PrefixCut := [⟨25,127917650,127917724⟩,
⟨106,537074180,537074493⟩,
⟨128,648153212,648153591⟩]
theorem checked19998 : checkPrefixCuts (2^48) 2625110017 9 Manual.Count131072.C019998.packed 128 cuts19998 = true := by
 decide +kernel
def pointBounds19998 : List (Nat × Nat × Nat) := [(2625135616,100019706216329,100020086585404),(2625218560,100020115372859,100020495742173)]
theorem point_links_checked19998 : (cuts19998.take 2).map (fun c => (2625110017-1+2*2^9*c.k,100019578298679+c.lower,100019958667680+c.upper)) = pointBounds19998 := by
 decide +kernel
def cuts19999 : List PrefixCut := [⟨59,295705753,295705926⟩,
⟨128,646834121,646834494⟩]
theorem checked19999 : checkPrefixCuts (2^48) 2625241089 9 Manual.Count131072.C019999.packed 128 cuts19999 = true := by
 decide +kernel
def pointBounds19999 : List (Nat × Nat × Nat) := [(2625301504,100020522157644,100020902527197)]
theorem point_links_checked19999 : (cuts19999.take 1).map (fun c => (2625241089-1+2*2^9*c.k,100020226451891+c.lower,100020606821271+c.upper)) = pointBounds19999 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000312
