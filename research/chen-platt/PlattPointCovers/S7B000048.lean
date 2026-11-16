import PlattPointSubsetKernel
import PlattPointPackets.S2B000221
import PlattPointPackets.S2B000222
import PlattPointPackets.S2B000223
import PlattPointPackets.S2B000224
import PlattPointPackets.S2B000225
import PlattGlobalGrid.S7B000048
namespace ChenEffective.PlattWindow.PointCovers.S7B000048
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000221.points ++ ChenEffective.PlattWindow.PointPackets.S2B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000223.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000224.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000225.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000048.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000048.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000048
