#include <iostream>
#include <fstream>
#include <vector>
#include <cstdint>
#include <string>

int main() {
    std::ifstream file("output_output.dat", std::ios::binary);
    if (!file) {
        std::cerr << "Cannot open file" << std::endl;
        return 1;
    }

    uint8_t type;
    while (file.read(reinterpret_cast<char*>(&type), sizeof(type))) {
        // 1. 共通のSeed読み込み
        uint64_t seed;
        file.read(reinterpret_cast<char*>(&seed), sizeof(seed));

        // 2. 共通のGraph6文字列読み込み (長さ -> 本体)
        int16_t g6_len;
        file.read(reinterpret_cast<char*>(&g6_len), sizeof(g6_len));
        
        std::string g6(g6_len, ' ');
        file.read(&g6[0], g6_len);

        if (type == 0) {
            // Independent Result
            std::cout << "[Independent] Seed: " << seed << ", G6: " << g6 << std::endl;
        } 
        else if (type == 1) {
            // Dependent Result
            int32_t class_index;
            file.read(reinterpret_cast<char*>(&class_index), sizeof(class_index));

            // C_indices (Vector<Int64> in Julia is usually 64bit)
            // JuliaのIntは64bit環境ならInt64です。C++側も合わせる必要があります。
            int16_t c_len;
            file.read(reinterpret_cast<char*>(&c_len), sizeof(c_len));
            std::vector<int64_t> c_indices(c_len);
            file.read(reinterpret_cast<char*>(c_indices.data()), c_len * sizeof(int64_t));

            // F_indices
            int16_t f_len;
            file.read(reinterpret_cast<char*>(&f_len), sizeof(f_len));
            std::vector<int64_t> f_indices(f_len);
            file.read(reinterpret_cast<char*>(f_indices.data()), f_len * sizeof(int64_t));

            std::cout << "[Dependent] Seed: " << seed << ", Class: " << class_index 
                      << ", Circuit Size: " << c_len << std::endl;
        }
        else if (type == 2) {
            // Forbidden
            std::cout << "[Forbidden] " << g6 << std::endl;
        }
    }

    return 0;
}