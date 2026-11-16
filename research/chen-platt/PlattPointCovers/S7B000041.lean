import PlattPointSubsetKernel
import PlattPointPackets.S2B000192
import PlattPointPackets.S2B000193
import PlattPointPackets.S2B000194
import PlattPointPackets.S2B000195
import PlattPointPackets.S2B000196
import PlattGlobalGrid.S7B000041
namespace ChenEffective.PlattWindow.PointCovers.S7B000041
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000192.points ++ ChenEffective.PlattWindow.PointPackets.S2B000193.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000195.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000196.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000041.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000041.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000041
