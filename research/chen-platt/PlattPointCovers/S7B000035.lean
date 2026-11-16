import PlattPointSubsetKernel
import PlattPointPackets.S2B000168
import PlattPointPackets.S2B000169
import PlattPointPackets.S2B000170
import PlattPointPackets.S2B000171
import PlattPointPackets.S2B000172
import PlattGlobalGrid.S7B000035
namespace ChenEffective.PlattWindow.PointCovers.S7B000035
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000168.points ++ ChenEffective.PlattWindow.PointPackets.S2B000169.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000170.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000171.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000172.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000035.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000035.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000035
