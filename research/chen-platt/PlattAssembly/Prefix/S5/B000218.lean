import PlattAssemblyKernel
import PlattCertificates.Count131072.C046976
import PlattCertificates.Count131072.C046977
import PlattCertificates.Count131072.C046978
import PlattCertificates.Count131072.C046979
import PlattCertificates.Count131072.C046980
import PlattCertificates.Count131072.C046981
import PlattCertificates.Count131072.C046982
import PlattCertificates.Count131072.C046983
import PlattCertificates.Count131072.C046984
import PlattCertificates.Count131072.C046985
import PlattCertificates.Count131072.C046986
import PlattCertificates.Count131072.C046987
import PlattCertificates.Count131072.C046988
import PlattCertificates.Count131072.C046989
import PlattCertificates.Count131072.C046990
import PlattCertificates.Count131072.C046991
import PlattCertificates.Count131072.C046992
import PlattCertificates.Count131072.C046993
import PlattCertificates.Count131072.C046994
import PlattCertificates.Count131072.C046995
import PlattCertificates.Count131072.C046996
import PlattCertificates.Count131072.C046997
import PlattCertificates.Count131072.C046998
import PlattCertificates.Count131072.C046999
import PlattCertificates.Count131072.C047000
import PlattCertificates.Count131072.C047001
import PlattCertificates.Count131072.C047002
import PlattCertificates.Count131072.C047003
import PlattCertificates.Count131072.C047004
import PlattCertificates.Count131072.C047005
import PlattCertificates.Count131072.C047006
import PlattCertificates.Count131072.C047007
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000218
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46976 : List PrefixCut := [⟨64,266890666,266890813⟩]
theorem checked46976 : checkPrefixCuts (2^48) 6161170433 10 Manual.Count131072.C046976.packed 64 cuts46976 = true := by
 decide +kernel
def cuts46977 : List PrefixCut := [⟨28,117316798,117316870⟩,
⟨64,270448306,270448461⟩]
theorem checked46977 : checkPrefixCuts (2^48) 6161301505 10 Manual.Count131072.C046977.packed 64 cuts46977 = true := by
 decide +kernel
def pointBounds46977 : List (Nat × Nat × Nat) := [(6161358848,110879804294185,110880190972265)]
theorem point_links_checked46977 : (cuts46977.take 1).map (fun c => (6161301505-1+2*2^10*c.k,110879686977387+c.lower,110880073655395+c.upper)) = pointBounds46977 := by
 decide +kernel
def cuts46978 : List PrefixCut := [⟨59,244403535,244403672⟩,
⟨64,265097672,265097820⟩]
theorem checked46978 : checkPrefixCuts (2^48) 6161432577 10 Manual.Count131072.C046978.packed 64 cuts46978 = true := by
 decide +kernel
def pointBounds46978 : List (Nat × Nat × Nat) := [(6161553408,110880201829228,110880588507528)]
theorem point_links_checked46978 : (cuts46978.take 1).map (fun c => (6161432577-1+2*2^10*c.k,110879957425693+c.lower,110880344103856+c.upper)) = pointBounds46978 := by
 decide +kernel
def cuts46979 : List PrefixCut := [⟨64,266005667,266005818⟩]
theorem checked46979 : checkPrefixCuts (2^48) 6161563649 10 Manual.Count131072.C046979.packed 64 cuts46979 = true := by
 decide +kernel
def cuts46980 : List PrefixCut := [⟨26,106300178,106300237⟩,
⟨64,265040712,265040861⟩]
theorem checked46980 : checkPrefixCuts (2^48) 6161694721 10 Manual.Count131072.C046980.packed 64 cuts46980 = true := by
 decide +kernel
def pointBounds46980 : List (Nat × Nat × Nat) := [(6161747968,110880594829210,110880981507731)]
theorem point_links_checked46980 : (cuts46980.take 1).map (fun c => (6161694721-1+2*2^10*c.k,110880488529032+c.lower,110880875207494+c.upper)) = pointBounds46980 := by
 decide +kernel
def cuts46981 : List PrefixCut := [⟨57,240459538,240459675⟩,
⟨64,269146275,269146430⟩]
theorem checked46981 : checkPrefixCuts (2^48) 6161825793 10 Manual.Count131072.C046981.packed 64 cuts46981 = true := by
 decide +kernel
def pointBounds46981 : List (Nat × Nat × Nat) := [(6161942528,110880994029282,110881380708030)]
theorem point_links_checked46981 : (cuts46981.take 1).map (fun c => (6161825793-1+2*2^10*c.k,110880753569744+c.lower,110881140248355+c.upper)) = pointBounds46981 := by
 decide +kernel
def cuts46982 : List PrefixCut := [⟨64,266171405,266171558⟩]
theorem checked46982 : checkPrefixCuts (2^48) 6161956865 10 Manual.Count131072.C046982.packed 64 cuts46982 = true := by
 decide +kernel
def cuts46983 : List PrefixCut := [⟨24,100218220,100218280⟩,
⟨64,268860760,268860916⟩]
theorem checked46983 : checkPrefixCuts (2^48) 6162087937 10 Manual.Count131072.C046983.packed 64 cuts46983 = true := by
 decide +kernel
def pointBounds46983 : List (Nat × Nat × Nat) := [(6162137088,110881389105644,110881775784623)]
theorem point_links_checked46983 : (cuts46983.take 1).map (fun c => (6162087937-1+2*2^10*c.k,110881288887424+c.lower,110881675566343+c.upper)) = pointBounds46983 := by
 decide +kernel
def cuts46984 : List PrefixCut := [⟨55,220620412,220620542⟩,
⟨64,257024676,257024828⟩]
theorem checked46984 : checkPrefixCuts (2^48) 6162219009 10 Manual.Count131072.C046984.packed 64 cuts46984 = true := by
 decide +kernel
def pointBounds46984 : List (Nat × Nat × Nat) := [(6162331648,110881778368596,110882165047801)]
theorem point_links_checked46984 : (cuts46984.take 1).map (fun c => (6162219009-1+2*2^10*c.k,110881557748184+c.lower,110881944427259+c.upper)) = pointBounds46984 := by
 decide +kernel
def cuts46985 : List PrefixCut := [⟨64,269077701,269077857⟩]
theorem checked46985 : checkPrefixCuts (2^48) 6162350081 10 Manual.Count131072.C046985.packed 64 cuts46985 = true := by
 decide +kernel
def cuts46986 : List PrefixCut := [⟨22,89615158,89615209⟩,
⟨64,264732834,264732983⟩]
theorem checked46986 : checkPrefixCuts (2^48) 6162481153 10 Manual.Count131072.C046986.packed 64 cuts46986 = true := by
 decide +kernel
def pointBounds46986 : List (Nat × Nat × Nat) := [(6162526208,110882173465719,110882560145153)]
theorem point_links_checked46986 : (cuts46986.take 1).map (fun c => (6162481153-1+2*2^10*c.k,110882083850561+c.lower,110882470529944+c.upper)) = pointBounds46986 := by
 decide +kernel
def cuts46987 : List PrefixCut := [⟨53,225310854,225310978⟩,
⟨64,270573511,270573660⟩]
theorem checked46987 : checkPrefixCuts (2^48) 6162612225 10 Manual.Count131072.C046987.packed 64 cuts46987 = true := by
 decide +kernel
def pointBounds46987 : List (Nat × Nat × Nat) := [(6162720768,110882573894249,110882960573905)]
theorem point_links_checked46987 : (cuts46987.take 1).map (fun c => (6162612225-1+2*2^10*c.k,110882348583395+c.lower,110882735262927+c.upper)) = pointBounds46987 := by
 decide +kernel
def cuts46988 : List PrefixCut := [⟨64,270522087,270522243⟩]
theorem checked46988 : checkPrefixCuts (2^48) 6162743297 10 Manual.Count131072.C046988.packed 64 cuts46988 = true := by
 decide +kernel
def cuts46989 : List PrefixCut := [⟨20,83306656,83306708⟩,
⟨64,264076536,264076687⟩]
theorem checked46989 : checkPrefixCuts (2^48) 6162874369 10 Manual.Count131072.C046989.packed 64 cuts46989 = true := by
 decide +kernel
def pointBounds46989 : List (Nat × Nat × Nat) := [(6162915328,110882972985649,110883359665538)]
theorem point_links_checked46989 : (cuts46989.take 1).map (fun c => (6162874369-1+2*2^10*c.k,110882889678993+c.lower,110883276358830+c.upper)) = pointBounds46989 := by
 decide +kernel
def cuts46990 : List PrefixCut := [⟨51,209996656,209996782⟩,
⟨64,264025240,264025397⟩]
theorem checked46990 : checkPrefixCuts (2^48) 6163005441 10 Manual.Count131072.C046990.packed 64 cuts46990 = true := by
 decide +kernel
def pointBounds46990 : List (Nat × Nat × Nat) := [(6163109888,110883363752185,110883750432299)]
theorem point_links_checked46990 : (cuts46990.take 1).map (fun c => (6163005441-1+2*2^10*c.k,110883153755529+c.lower,110883540435517+c.upper)) = pointBounds46990 := by
 decide +kernel
def cuts46991 : List PrefixCut := [⟨64,263928263,263928420⟩]
theorem checked46991 : checkPrefixCuts (2^48) 6163136513 10 Manual.Count131072.C046991.packed 64 cuts46991 = true := by
 decide +kernel
def cuts46992 : List PrefixCut := [⟨18,75217854,75217901⟩,
⟨64,268580943,268581098⟩]
theorem checked46992 : checkPrefixCuts (2^48) 6163267585 10 Manual.Count131072.C046992.packed 64 cuts46992 = true := by
 decide +kernel
def pointBounds46992 : List (Nat × Nat × Nat) := [(6163304448,110883756926886,110884143607235)]
theorem point_links_checked46992 : (cuts46992.take 1).map (fun c => (6163267585-1+2*2^10*c.k,110883681709032+c.lower,110884068389334+c.upper)) = pointBounds46992 := by
 decide +kernel
def cuts46993 : List PrefixCut := [⟨49,203315754,203315865⟩,
⟨64,267524855,267525001⟩]
theorem checked46993 : checkPrefixCuts (2^48) 6163398657 10 Manual.Count131072.C046993.packed 64 cuts46993 = true := by
 decide +kernel
def pointBounds46993 : List (Nat × Nat × Nat) := [(6163499008,110884153605729,110884540286297)]
theorem point_links_checked46993 : (cuts46993.take 1).map (fun c => (6163398657-1+2*2^10*c.k,110883950289975+c.lower,110884336970432+c.upper)) = pointBounds46993 := by
 decide +kernel
def cuts46994 : List PrefixCut := [⟨64,267884481,267884632⟩]
theorem checked46994 : checkPrefixCuts (2^48) 6163529729 10 Manual.Count131072.C046994.packed 64 cuts46994 = true := by
 decide +kernel
def cuts46995 : List PrefixCut := [⟨16,66079736,66079775⟩,
⟨64,265230171,265230323⟩]
theorem checked46995 : checkPrefixCuts (2^48) 6163660801 10 Manual.Count131072.C046995.packed 64 cuts46995 = true := by
 decide +kernel
def pointBounds46995 : List (Nat × Nat × Nat) := [(6163693568,110884551779047,110884938459840)]
theorem point_links_checked46995 : (cuts46995.take 1).map (fun c => (6163660801-1+2*2^10*c.k,110884485699311+c.lower,110884872380065+c.upper)) = pointBounds46995 := by
 decide +kernel
def cuts46996 : List PrefixCut := [⟨47,193484782,193484894⟩,
⟨64,264037245,264037397⟩]
theorem checked46996 : checkPrefixCuts (2^48) 6163791873 10 Manual.Count131072.C046996.packed 64 cuts46996 = true := by
 decide +kernel
def pointBounds46996 : List (Nat × Nat × Nat) := [(6163888128,110884944414264,110885331095282)]
theorem point_links_checked46996 : (cuts46996.take 1).map (fun c => (6163791873-1+2*2^10*c.k,110884750929482+c.lower,110885137610388+c.upper)) = pointBounds46996 := by
 decide +kernel
def cuts46997 : List PrefixCut := [⟨64,264031629,264031771⟩]
theorem checked46997 : checkPrefixCuts (2^48) 6163922945 10 Manual.Count131072.C046997.packed 64 cuts46997 = true := by
 decide +kernel
def cuts46998 : List PrefixCut := [⟨14,59865262,59865297⟩,
⟨64,264802297,264802457⟩]
theorem checked46998 : checkPrefixCuts (2^48) 6164054017 10 Manual.Count131072.C046998.packed 64 cuts46998 = true := by
 decide +kernel
def pointBounds46998 : List (Nat × Nat × Nat) := [(6164082688,110885338863618,110885725544853)]
theorem point_links_checked46998 : (cuts46998.take 1).map (fun c => (6164054017-1+2*2^10*c.k,110885278998356+c.lower,110885665679556+c.upper)) = pointBounds46998 := by
 decide +kernel
def cuts46999 : List PrefixCut := [⟨45,187673326,187673431⟩,
⟨64,264340038,264340186⟩]
theorem checked46999 : checkPrefixCuts (2^48) 6164185089 10 Manual.Count131072.C046999.packed 64 cuts46999 = true := by
 decide +kernel
def pointBounds46999 : List (Nat × Nat × Nat) := [(6164277248,110885731473979,110886118155444)]
theorem point_links_checked46999 : (cuts46999.take 1).map (fun c => (6164185089-1+2*2^10*c.k,110885543800653+c.lower,110885930482013+c.upper)) = pointBounds46999 := by
 decide +kernel
def cuts47000 : List PrefixCut := [⟨64,263329853,263330002⟩]
theorem checked47000 : checkPrefixCuts (2^48) 6164316161 10 Manual.Count131072.C047000.packed 64 cuts47000 = true := by
 decide +kernel
def cuts47001 : List PrefixCut := [⟨12,49359455,49359483⟩,
⟨64,264100485,264100634⟩]
theorem checked47001 : checkPrefixCuts (2^48) 6164447233 10 Manual.Count131072.C047001.packed 64 cuts47001 = true := by
 decide +kernel
def pointBounds47001 : List (Nat × Nat × Nat) := [(6164471808,110886120829999,110886507511684)]
theorem point_links_checked47001 : (cuts47001.take 1).map (fun c => (6164447233-1+2*2^10*c.k,110886071470544+c.lower,110886458152201+c.upper)) = pointBounds47001 := by
 decide +kernel
def cuts47002 : List PrefixCut := [⟨43,178301191,178301291⟩,
⟨64,267564981,267565130⟩]
theorem checked47002 : checkPrefixCuts (2^48) 6164578305 10 Manual.Count131072.C047002.packed 64 cuts47002 = true := by
 decide +kernel
def pointBounds47002 : List (Nat × Nat × Nat) := [(6164666368,110886513872220,110886900554126)]
theorem point_links_checked47002 : (cuts47002.take 1).map (fun c => (6164578305-1+2*2^10*c.k,110886335571029+c.lower,110886722252835+c.upper)) = pointBounds47002 := by
 decide +kernel
def cuts47003 : List PrefixCut := [⟨64,265230703,265230854⟩]
theorem checked47003 : checkPrefixCuts (2^48) 6164709377 10 Manual.Count131072.C047003.packed 64 cuts47003 = true := by
 decide +kernel
def cuts47004 : List PrefixCut := [⟨10,42096696,42096721⟩,
⟨64,263307489,263307638⟩]
theorem checked47004 : checkPrefixCuts (2^48) 6164840449 10 Manual.Count131072.C047004.packed 64 cuts47004 = true := by
 decide +kernel
def pointBounds47004 : List (Nat × Nat × Nat) := [(6164860928,110886910463409,110887297145540)]
theorem point_links_checked47004 : (cuts47004.take 1).map (fun c => (6164840449-1+2*2^10*c.k,110886868366713+c.lower,110887255048819+c.upper)) = pointBounds47004 := by
 decide +kernel
def cuts47005 : List PrefixCut := [⟨41,170528228,170528325⟩,
⟨64,265493406,265493555⟩]
theorem checked47005 : checkPrefixCuts (2^48) 6164971521 10 Manual.Count131072.C047005.packed 64 cuts47005 = true := by
 decide +kernel
def pointBounds47005 : List (Nat × Nat × Nat) := [(6165055488,110887302202430,110887688884782)]
theorem point_links_checked47005 : (cuts47005.take 1).map (fun c => (6164971521-1+2*2^10*c.k,110887131674202+c.lower,110887518356457+c.upper)) = pointBounds47005 := by
 decide +kernel
def cuts47006 : List PrefixCut := [⟨64,262748396,262748547⟩]
theorem checked47006 : checkPrefixCuts (2^48) 6165102593 10 Manual.Count131072.C047006.packed 64 cuts47006 = true := by
 decide +kernel
def cuts47007 : List PrefixCut := [⟨8,33647829,33647847⟩,
⟨64,266075603,266075752⟩]
theorem checked47007 : checkPrefixCuts (2^48) 6165233665 10 Manual.Count131072.C047007.packed 64 cuts47007 = true := by
 decide +kernel
def pointBounds47007 : List (Nat × Nat × Nat) := [(6165250048,110887693563833,110888080246406)]
theorem point_links_checked47007 : (cuts47007.take 1).map (fun c => (6165233665-1+2*2^10*c.k,110887659916004+c.lower,110888046598559+c.upper)) = pointBounds47007 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000218
